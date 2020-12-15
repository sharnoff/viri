//! Macros for defining and using attributes
//!
//! There's a more detailed explanation in the `config::attr` submodule in the main crate. Please
//! refer there for additional information. Documentation for the macros can be found where they are
//! re-exported (in the `macros` submodule).

use derive_syn_parse::Parse;
use proc_macro::TokenStream;
use quote::{format_ident, quote, quote_spanned};
use std::sync::atomic::{AtomicU16, AtomicUsize, Ordering};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{parse_macro_input, token, Attribute, Expr, Ident, Token, Type, Visibility};

// Meta-note: Fields with the name `attr(s)` refer to item attributes, not "attributes" as used in
// the editor.

/// The input to the `new_attrs!` macro
#[derive(Parse)]
struct NewAttrsInput {
    #[parse_terminated(AttrDefinition::parse)]
    inner: Punctuated<AttrDefinition, Token![,]>,
}

#[derive(Parse)]
struct AttrDefinition {
    #[call(Attribute::parse_outer)]
    attrs: Vec<Attribute>,
    vis: Visibility,
    name: Ident,
    _colon: Token![:],
    ty: Type,
    _eq: Token![=],
    expr: Expr,
}

pub fn new_attrs(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as NewAttrsInput);

    static NEXT_ATTR_ID: AtomicU16 = AtomicU16::new(0);

    let iter = input.inner.into_iter().map(|attr_def| {
        #[rustfmt::skip]
        let AttrDefinition { attrs, vis, name, ty, expr, ..  } = attr_def;
        let value = NEXT_ATTR_ID.fetch_add(1, Ordering::SeqCst);

        let const_value = quote_spanned! {
            name.span()=>
            impl crate::config::attr::Attribute {
                #( #attrs )*
                #[allow(non_upper_case_globals)]
                #vis const #name: Self = crate::config::attr::Attribute::from(#value);
            }
        };

        let token = quote! {
            crate::config::attr::AttrToken<{crate::config::attr::Attribute::#name}>
        };

        let name_as_str = name.to_string();

        let inventory = quote_spanned! {
            name.span()=>
            ::inventory::submit!(crate::config::attr::AttributeDefinition::new(
                #name_as_str,
                crate::config::attr::Attribute::#name,
                crate::any::Type::new::<#ty>(),
                || crate::any::BoxedAny::new(<#token as crate::config::attr::TypedAttr>::default_value()),
            ));
        };

        let impl_typedattr = quote_spanned! {
            ty.span()=>
            impl crate::config::attr::TypedAttr for #token {
                type Type = #ty;

                fn default_value() -> Self::Type {
                    #expr
                }
            }
        };

        quote!(
            #const_value
            #inventory
            #impl_typedattr
        )
    });

    quote!( #( #iter )* ).into()
}

/// Input for the `provide_attrs!` macro
#[derive(Parse)]
struct ProvideAttrsInput {
    base_ty: Type,
    _right_arrow: Token![=>],
    #[brace]
    _brace: token::Brace,
    #[inside(_brace)]
    #[parse_terminated(AttrValue::parse)]
    values: Punctuated<AttrValue, Token![,]>,
}

#[derive(Parse)]
struct AttrValue {
    name: Ident,
    _right_arrow: Token![=>],
    expr: Expr,
}

pub fn provide_attrs(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as ProvideAttrsInput);
    let base_ty = input.base_ty;

    let base_ty_as_cfg_type = quote_spanned! {
        base_ty.span()=>
        std::any::TypeId::of::<#base_ty>()
    };

    let downcast_to_self = quote_spanned! {
        base_ty.span()=>
        this.downcast_ref::<#base_ty>()
            .expect(&format!(
                "unexpected type provided as input, expected `{}`",
                std::any::type_name::<#base_ty>(),
            ))
    };

    let impls = (input.values)
        .into_iter()
        .map(|AttrValue { name, expr, .. }| {
            let attr_value = quote_spanned! {
                name.span()=>
                crate::config::attr::Attribute::#name
            };

            let expr_span = expr.span();
            let span = expr_span.join(name.span()).unwrap_or(expr_span);

            let func_name = generate_wrapper_fn_name(&name);
            let wrapper_func = quote_spanned! {
                span=>
                #[allow(non_snake_case)]
                #[viri_macros::async_method]
                async fn #func_name ( this: &dyn std::any::Any + 'static + Send + Sync )
                        -> crate::any::BoxedAny {
                    // Downcast `this` into the base type we're implementing on
                    let this = #downcast_to_self;

                    impl #base_ty {
                        #[allow(non_snake_case)]
                        async fn #func_name(&self) -> viri_macros::attr_type![#attr_value] {
                            #expr
                        }
                    }

                    crate::any::BoxedAny::new(this.#func_name().await)
                }
            };

            quote_spanned! {
                span=>
                #wrapper_func

                ::inventory::submit!(crate::config::attr::AttributeImplementation::new(
                    #base_ty_as_cfg_type,
                    #attr_value,
                    #func_name,
                ));
            }
        });

    quote!(
        #( #impls )*
    )
    .into()
}

fn generate_wrapper_fn_name(name: &Ident) -> Ident {
    static WRAPPER_COUNTER: AtomicUsize = AtomicUsize::new(0);

    let count = WRAPPER_COUNTER.fetch_add(1, Ordering::SeqCst);

    format_ident!("__{}_wrapper_{}", name, count)
}

// Note: exported as AttrType from `viri::macros`
pub fn attr_type(input: TokenStream) -> TokenStream {
    let expr = parse_macro_input!(input as Expr);

    quote_spanned!(
        expr.span()=>
        <crate::config::attr::AttrToken<{#expr}> as crate::config::attr::TypedAttr>::Type
    )
    .into()
}

pub fn impl_get_attr_any(input: TokenStream) -> TokenStream {
    let ty = parse_macro_input!(input as Type);

    quote_spanned! (
        ty.span()=>
        impl crate::config::GetAttrAny for #ty {
            #[crate::macros::async_method]
            async fn get_attr_any(
                &self,
                attr: crate::config::Attribute
            ) -> Option<crate::any::BoxedAny> {
                crate::config::attr::get_attr_any(self, attr).await
            }
        }
    )
    .into()
}
