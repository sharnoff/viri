//! Macro(s) for help with configuration

use derive_syn_parse::Parse;
use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{quote, quote_spanned, ToTokens};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{
    braced, parenthesized, parse_macro_input, token, Attribute, Expr, Ident, Path, Token, Type,
    Visibility,
};

struct ConfigInput {
    static_src: Option<StaticSource>,
    attrs: Vec<Attribute>,
    vis: Visibility,
    ident: Ident,
    builder_name: Ident,
    struct_body: Punctuated<StructField, Token![,]>,
}

#[derive(Default)]
struct MacroBuilder {
    config_fields: Vec<TokenStream2>,
    builder_fields: Vec<TokenStream2>,
    from_builder_fields: Vec<TokenStream2>,
    to_builder_fields: Vec<TokenStream2>,
    validate_calls: Vec<TokenStream2>,
}

#[rustfmt::skip]
pub fn config(input: TokenStream) -> TokenStream {
    let cfg_input = parse_macro_input!(input as ConfigInput);
    let ConfigInput {
        static_src, attrs, vis, ident, builder_name, struct_body,
    } = cfg_input;

    let mut macro_builder = MacroBuilder::default();

    let mut errors = Vec::new();

    // TODO:
    // Just as `impl_config` will implement `ChildConfig`, we need to provide each child config type
    // with an implementation of `Configurable` -- because we're the parent and only we know how to
    // get the global configuration.
    let impl_for_children = (struct_body.iter())
        .filter_map(|field| match field {
            StructField::Use(use_field) => Some(use_field),
            StructField::Normal(_) => None,
        })
        .map(|use_field| {
            let path = &use_field.path;
            let field_ident = &use_field.ident;

            quote! {
                impl crate::config::Configurable for #path {
                    type Builder = <Self as crate::config::ChildConfig>::Builder;

                    fn get_global() -> std::sync::Arc<Self> {
                        <#ident as crate::config::Configurable>::get_global().#field_ident.clone()
                    }

                    fn to_builder(&self) -> Self::Builder {
                        <Self as crate::config::ChildConfig>::to_builder(self)
                    }
                }
            }
        })
        .collect::<Vec<_>>();

    for field in struct_body {
        process_field(field, &mut macro_builder, &mut errors);
    }

    if !errors.is_empty() {
        return errors.into_iter().map(|e| e.to_compile_error()).collect::<TokenStream2>().into();
    }

    let MacroBuilder {
        config_fields,
        builder_fields,
        from_builder_fields,
        to_builder_fields,
        validate_calls,
    } = macro_builder;

    let config_struct_item = quote_spanned! {ident.span()=>
        #( #attrs )*
        #vis struct #ident {
            #( #config_fields, )*
        }
    };

    let build_struct_item = quote_spanned! {builder_name.span()=>
        #[derive(Debug, Default, serde::Serialize, serde::Deserialize)]
        #vis struct #builder_name {
            #( #builder_fields, )*
        }
    };

    let impl_from_builder = quote! {
        impl From<#builder_name> for #ident {
            fn from(builder: #builder_name) -> Self {
                use arc_swap::ArcSwap;
                use std::sync::Arc;

                let this = Self {
                    #( #from_builder_fields, )*
                };

                this
            }
        }
    };

    // A helper for `impl_config`
    let to_builder = quote! {
        fn to_builder(&self) -> #builder_name {
            #builder_name {
                #( #to_builder_fields, )*
            }
        }
    };

    let impl_config = match static_src.as_ref() {
        #[rustfmt::skip] // Keep the fields on a single line
        Some(StaticSource {
            attrs, vis, ident: static_name, ..
        }) => quote! {
            lazy_static::lazy_static! {
                #( #attrs )*
                #vis static ref #static_name: arc_swap::ArcSwapOption<#ident>
                    = arc_swap::ArcSwapAny::empty();
            }

            impl crate::config::Configurable for #ident {
                type Builder = #builder_name;

                fn get_global() -> std::sync::Arc<Self> {
                    #static_name.load().as_ref().unwrap().clone()
                }

                #to_builder
            }
        },
        None => quote! {
            impl crate::config::ChildConfig for #ident {
                type Builder = #builder_name;

                #to_builder
            }
        },
    };
    
    let impl_validate = quote! {
        impl #ident {
            /// Validates the configuration, returning the first error that occurs
            pub fn validate(&self) -> Result<(), String> {
                #( #validate_calls?; )*

                Ok(())
            }
        }
    };

    quote!(
        #config_struct_item
        #build_struct_item
        #impl_from_builder
        #impl_config
        #impl_validate
        #(#impl_for_children)*
    )
    .into()
}

fn process_field(field: StructField, ctx: &mut MacroBuilder, errors: &mut Vec<syn::Error>) {
    match field {
        StructField::Use(f) => process_use_field(f, ctx, errors),
        StructField::Normal(f) => process_normal_field(f, ctx, errors),
    }
}

fn process_use_field(field: UseField, ctx: &mut MacroBuilder, errors: &mut Vec<syn::Error>) {
    let UseField {
        attrs,
        vis,
        path: config_ty,
        ident,
        ..
    } = field;

    let (attrs, mut custom_attrs) = match parse_custom_attrs(attrs, errors) {
        Ok(tuple) => tuple,
        Err(()) => return,
    };

    ctx.validate_calls
        .push(quote_spanned!(config_ty.span()=> self.#ident.validate()));

    custom_attrs
        .drain_filter(|attr| match attr {
            CustomAttr::ValidateWith(_, _) => true,
            _ => false,
        })
        .filter_map(|attr| match attr {
            CustomAttr::ValidateWith(span, expr) => Some((span, expr)),
            _ => None,
        })
        .for_each(|(_span, expr)| {
            ctx.validate_calls
                .push(quote!((#expr)(&self.#ident as &#config_ty)))
        });

    let builder_ty;
    let maybe_flattened_attr;
    let from_builder_expr;
    let into_builder_expr;

    if custom_attrs.len() > 1 {
        errors.push(syn::Error::new(
            custom_attrs[0].span(),
            "Cannot have more than one config field attribute",
        ));
        return;
    } else if custom_attrs.len() == 1 {
        let flatten_span = match custom_attrs.remove(0) {
            CustomAttr::Flatten(span) => span,
            CustomAttr::BuilderType { 0: span, .. } => {
                errors.push(syn::Error::new(
                    span,
                    "Builders cannot be specified for sub-configurations",
                ));
                return;
            }
            // unreachable because we filter them out above:
            CustomAttr::ValidateWith(_, _) => unreachable!(),
        };

        builder_ty =
            quote_spanned!(config_ty.span()=> <#config_ty as crate::config::ChildConfig>::Builder);
        maybe_flattened_attr = quote_spanned!(flatten_span=> #[serde(flatten)]);
        from_builder_expr = quote_spanned!(config_ty.span()=> builder.#ident.into());
        into_builder_expr = quote_spanned!(config_ty.span()=> <#config_ty as crate::config::ChildConfig>::to_builder(&self.#ident));
    } else {
        builder_ty = quote_spanned!(config_ty.span()=> Option<<#config_ty as crate::config::ChildConfig>::Builder>);
        maybe_flattened_attr = TokenStream2::new();

        from_builder_expr =
            quote_spanned!(config_ty.span()=> builder.#ident.unwrap_or_default().into());
        into_builder_expr = quote_spanned!(config_ty.span()=> Some(<#config_ty as crate::config::ChildConfig>::to_builder(&self.#ident)));
    }

    ctx.config_fields.push(quote! {
        #( #attrs )* #vis #ident: std::sync::Arc<#config_ty>
    });

    ctx.builder_fields.push(quote!(
        #maybe_flattened_attr
        #ident: #builder_ty
    ));

    ctx.from_builder_fields
        .push(quote!(#ident: std::sync::Arc::new(#from_builder_expr)));

    ctx.to_builder_fields
        .push(quote!(#ident: #into_builder_expr));
}

fn process_normal_field(field: Field, ctx: &mut MacroBuilder, errors: &mut Vec<syn::Error>) {
    let Field {
        attrs,
        vis,
        ident,
        _colon: _,
        ty,
        default_value,
    } = field;

    let (attrs, mut custom_attrs) = match parse_custom_attrs(attrs, errors) {
        Ok(tuple) => tuple,
        Err(()) => return,
    };

    custom_attrs
        .drain_filter(|attr| match attr {
            CustomAttr::ValidateWith(_, _) => true,
            _ => false,
        })
        .filter_map(|attr| match attr {
            CustomAttr::ValidateWith(span, expr) => Some((span, expr)),
            _ => None,
        })
        .for_each(|(_span, expr)| {
            ctx.validate_calls
                .push(quote_spanned!(expr.span()=> (#expr)(&self.#ident.load() as &#ty)))
        });

    let builder_ty;
    let from_builder_expr;
    let into_builder_expr;

    if custom_attrs.len() > 1 {
        errors.push(syn::Error::new(
            custom_attrs[0].span(),
            "Cannot have more than one complex config field attribute",
        ));
        return;
    } else if custom_attrs.len() == 1 {
        let (_span, build_ty, maybe_paths) = match custom_attrs.remove(0) {
            CustomAttr::BuilderType(a, b, c) => (a, b, c), // Ugh.
            CustomAttr::Flatten(span) => {
                errors.push(syn::Error::new(
                    span,
                    "Deserialization flattening is only permitted for sub-configurations",
                ));
                return;
            }
            // unreachable because we filter them out above:
            CustomAttr::ValidateWith(_, _) => unreachable!(),
        };

        if let Some(v) = default_value.as_ref() {
            errors.push(syn::Error::new(
                v.expr.span(),
                "this field does not need a default value since its builder is already provided",
            ));
        }

        builder_ty = build_ty.to_token_stream();

        if let Some((from_builder, into_builder)) = maybe_paths {
            from_builder_expr = quote_spanned! {
                from_builder.span()=>
                ArcSwap::new(Arc::new(#from_builder (builder.#ident)))
            };
            into_builder_expr = quote_spanned! {
                into_builder.span()=>
                #into_builder ( &self.#ident.load() as &#ty )
            };
        } else {
            let as_from_builder = quote_spanned! {
                build_ty.span()=>
                <#ty as crate::config::FromBuilder<#build_ty>>
            };

            from_builder_expr = quote_spanned! {
                build_ty.span()=>
                ArcSwap::new(Arc::new(#as_from_builder :: from_builder(builder.#ident)))
            };
            into_builder_expr = quote_spanned! {
                build_ty.span()=>
                #as_from_builder :: to_builder( &self.#ident.load() as &#ty )
            };
        }
    } else {
        let expr = match default_value {
            Some(default_value) => default_value.expr,
            None => {
                errors.push(syn::Error::new(
                    ident.span(),
                    "this field requires a default value; add `= <EXPR>`",
                ));
                return;
            }
        };

        builder_ty = quote_spanned!(ty.span()=> Option<#ty>);
        from_builder_expr = quote_spanned! {
            expr.span()=>
            ArcSwap::new(Arc::new(builder.#ident.unwrap_or_else(|| #expr)))
        };
        into_builder_expr = quote_spanned! {
            ty.span()=>
            Some(<#ty>::clone(&self.#ident.load()))
        };
    }

    let config_ty = quote_spanned!(ty.span()=> arc_swap::ArcSwap<#ty>);
    ctx.config_fields.push(quote! {
        #( #attrs )* #vis #ident: #config_ty
    });

    ctx.builder_fields.push(quote!(#ident: #builder_ty));

    ctx.from_builder_fields
        .push(quote!(#ident: #from_builder_expr));
    ctx.to_builder_fields
        .push(quote!(#ident: #into_builder_expr));
}

fn parse_custom_attrs(
    mut attrs: Vec<Attribute>,
    errors: &mut Vec<syn::Error>,
) -> Result<(Vec<Attribute>, Vec<CustomAttr>), ()> {
    let mut customs = Vec::new();
    let mut had_errors = false;
    attrs = attrs
        .into_iter()
        .filter_map(|attr| match CustomAttr::try_from(attr) {
            Err(original_attr) => Some(original_attr),
            Ok(Err(actual_error)) => {
                errors.push(actual_error);
                had_errors = true;
                None
            }
            Ok(Ok(custom_attr)) => {
                customs.push(custom_attr);
                None
            }
        })
        .collect();

    if had_errors {
        Err(())
    } else {
        Ok((attrs, customs))
    }
}

//////////////////
// Helper Types //
//////////////////

struct StaticSource {
    attrs: Vec<Attribute>,
    vis: Visibility,
    _static_token: Token![static],
    ident: Ident,
    _trailing_semi: Token![;],
}

enum StructField {
    Use(UseField),
    Normal(Field),
}

struct UseField {
    attrs: Vec<Attribute>,
    vis: Visibility,
    _use_kwd: Token![use],
    path: Path,
    _as_kwd: Token![as],
    ident: Ident,
}

struct Field {
    attrs: Vec<Attribute>,
    vis: Visibility,
    ident: Ident,
    _colon: Token![:],
    ty: Type,
    default_value: Option<DefaultValue>,
}

struct DefaultValue {
    _eq: Token![=],
    expr: Expr,
}

enum CustomAttr {
    Flatten(Span),
    // The span for the attribute, replacement type for the builder, the function to convert from
    // from the builder type to the normal type, and the function to go in the opposite direction.
    BuilderType(Span, Type, Option<(Path, Path)>),
    ValidateWith(Span, Expr),
}

impl Spanned for CustomAttr {
    fn span(&self) -> Span {
        match self {
            CustomAttr::Flatten(s) => s.clone(),
            CustomAttr::BuilderType { 0: s, .. } => s.clone(),
            CustomAttr::ValidateWith(s, _) => s.clone(),
        }
    }
}

///////////////////////////
// Parse Implementations //
///////////////////////////

impl Parse for ConfigInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut attrs = input.call(Attribute::parse_outer)?;
        let mut vis = input.parse()?;

        let static_src = if input.peek(Token![static]) {
            let src = Some(StaticSource::parse_from_static(input, attrs, vis)?);

            attrs = input.call(Attribute::parse_outer)?;
            vis = input.parse()?;

            src
        } else {
            None
        };

        input.parse::<Token![struct]>()?;

        Ok(ConfigInput {
            static_src,
            attrs,
            vis,
            ident: input.parse()?,
            builder_name: {
                let build_parens;
                parenthesized!(build_parens in input);
                let name = build_parens.parse()?;
                if !build_parens.is_empty() {
                    return Err(input.error("expected closing ')'"));
                }
                name
            },
            struct_body: {
                let struct_curlies;
                braced!(struct_curlies in input);
                struct_curlies.parse_terminated(StructField::parse)?
            },
        })
    }
}

impl StaticSource {
    fn parse_from_static(
        input: ParseStream,
        attrs: Vec<Attribute>,
        vis: Visibility,
    ) -> syn::Result<Self> {
        Ok(StaticSource {
            attrs,
            vis,
            _static_token: input.parse()?,
            ident: input.parse()?,
            _trailing_semi: input.parse()?,
        })
    }
}

impl Parse for StructField {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let vis = input.parse()?;

        if input.peek(Token![use]) {
            UseField::continue_parse(attrs, vis, input).map(StructField::Use)
        } else if input.peek(Ident) {
            Field::continue_parse(attrs, vis, input).map(StructField::Normal)
        } else {
            Err(input.error("expected keyword `use` or identifier"))
        }
    }
}

impl UseField {
    fn continue_parse(
        attrs: Vec<Attribute>,
        vis: Visibility,
        input: ParseStream,
    ) -> syn::Result<Self> {
        Ok(UseField {
            attrs,
            vis,
            _use_kwd: input.parse()?,
            path: input.parse()?,
            _as_kwd: input.parse()?,
            ident: input.parse()?,
        })
    }
}

impl Field {
    fn continue_parse(
        attrs: Vec<Attribute>,
        vis: Visibility,
        input: ParseStream,
    ) -> syn::Result<Self> {
        Ok(Field {
            attrs,
            vis,
            ident: input.parse()?,
            _colon: input.parse()?,
            ty: input.parse()?,
            default_value: DefaultValue::try_parse(input)?,
        })
    }
}

impl DefaultValue {
    fn try_parse(input: ParseStream) -> syn::Result<Option<Self>> {
        if !input.peek(Token![=]) {
            return Ok(None);
        }

        Ok(Some(DefaultValue {
            _eq: input.parse()?,
            expr: input.parse()?,
        }))
    }
}

impl CustomAttr {
    // Attempts to parse an attribute as one of the attributes we'll deal with
    //
    // If it isn't one of the ones we're expecting, we return the original attribute we were
    // expecting
    fn try_from(attr: Attribute) -> Result<syn::Result<CustomAttr>, Attribute> {
        // We're expecting either of:
        //   #[builder($TYPE)]
        //   #[builder($TYPE => $PATH, $PATH)]
        // or
        //   #[flatten]
        // Anything else isn't one of our attributes.

        let span = attr.span();
        let ident = match attr.path.get_ident() {
            Some(id) => id,
            None => return Err(attr),
        };

        match ident.to_string().as_str() {
            "builder" => Ok(CustomAttr::parse_builder(span, attr.tokens)),
            "flatten" => Ok(CustomAttr::parse_flatten(span, attr.tokens)),
            "validate_with" => Ok(CustomAttr::parse_validate_with(span, attr.tokens)),
            _ => Err(attr),
        }
    }

    fn parse_builder(span: Span, tokens: TokenStream2) -> syn::Result<Self> {
        struct BuilderAttr {
            _paren_token: token::Paren,
            ty: Type,
            tail: Option<BuilderTail>,
        }

        struct BuilderTail {
            _arrow: Token![=>],
            from_builder: Path,
            _comma: Token![,],
            into_builder: Path,
        }

        impl Parse for BuilderAttr {
            fn parse(input: ParseStream) -> syn::Result<Self> {
                let paren;
                Ok(BuilderAttr {
                    _paren_token: parenthesized!(paren in input),
                    ty: paren.parse()?,
                    tail: BuilderTail::try_parse(&paren)?,
                })
            }
        }

        impl BuilderTail {
            fn try_parse(input: ParseStream) -> syn::Result<Option<Self>> {
                if !input.peek(Token![=>]) {
                    return Ok(None);
                }

                Ok(Some(BuilderTail {
                    _arrow: input.parse()?,
                    from_builder: input.parse()?,
                    _comma: input.parse()?,
                    into_builder: input.parse()?,
                }))
            }
        }

        syn::parse2::<BuilderAttr>(tokens).map(move |attr| {
            let tail = attr.tail.map(|t| (t.from_builder, t.into_builder));
            CustomAttr::BuilderType(span, attr.ty, tail)
        })
    }

    fn parse_flatten(span: Span, tokens: TokenStream2) -> syn::Result<Self> {
        struct Empty;

        impl Parse for Empty {
            fn parse(_input: ParseStream) -> syn::Result<Self> {
                Ok(Empty)
            }
        }

        syn::parse2(tokens).map(move |Empty| CustomAttr::Flatten(span))
    }

    fn parse_validate_with(span: Span, tokens: TokenStream2) -> syn::Result<Self> {
        #[derive(Parse)]
        struct ValidateWith {
            #[paren]
            _paren_token: token::Paren,
            #[inside(_paren_token)]
            func: Expr,
        }

        syn::parse2::<ValidateWith>(tokens).map(move |val| CustomAttr::ValidateWith(span, val.func))
    }
}
