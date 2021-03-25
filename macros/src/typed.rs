//! Handling of extension handler type signatures

use derive_syn_parse::Parse;
use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{quote, quote_spanned, ToTokens, TokenStreamExt};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{parse_macro_input, token, Data, DeriveInput, Expr, Generics, Ident, Path, Token};

use super::{parse_repeated, AtKwd};

keywords! { mod kwd = any, int, string, repr, clone_with }

/// A custom rust-like type signature, essentially identical in structure to
/// `viri::dispatch::TypeRepr`
#[derive(Parse)]
enum Type {
    #[peek_with(at_kwd![any], name = "`@any`")]
    Any(AtKwd<kwd::any>),

    #[peek(token::Paren, name = "unit (`()`)")]
    Unit(#[paren] token::Paren),

    #[peek_with(at_kwd![any], name = "`@int`")]
    Int(AtKwd<kwd::int>),

    #[peek_with(at_kwd![string], name = "`@string`")]
    String(AtKwd<kwd::string>),

    #[peek(Token![enum], name = "`enum`")]
    Enum(Token![enum], Variants),

    #[peek(token::Brace, name = "struct (`{` .. `}`)")]
    Struct(Fields),

    #[peek(token::Bracket, name = "array (`[` <type> `]`)")]
    Array(ArrayType),

    #[peek(token::Paren, name = "tuple (`(` .. `)`)")]
    Tuple(TupleType),

    // Peeking for a path is a little tricky; we'll just not do it
    #[peek_with(|_| true, name = "ident")]
    Named(Path),
}

#[derive(Parse)]
struct ArrayType {
    #[bracket]
    bracket: token::Bracket,
    #[inside(bracket)]
    ty: Box<Type>,
}

#[derive(Parse)]
struct TupleType {
    #[paren]
    paren: token::Paren,
    #[inside(paren)]
    #[parse_terminated(Type::parse)]
    tys: Punctuated<Type, Token![,]>,
}

/// Enum variants
#[derive(Parse)]
struct Variants {
    #[brace]
    brace: token::Brace,

    #[inside(brace)]
    #[parse_terminated(Variant::parse)]
    vs: Punctuated<Variant, Token![,]>,
}

/// An individual variant of an enum
#[derive(Parse)]
struct Variant {
    name: Ident,
    colon: Option<Token![:]>,
    #[parse_if(colon.is_some())]
    ty: Option<Type>,
}

#[derive(Parse)]
struct Fields {
    #[brace]
    brace: token::Brace,

    #[inside(brace)]
    #[parse_terminated(Field::parse)]
    fs: Punctuated<Field, Token![,]>,
}

#[derive(Parse)]
struct Field {
    name: Ident,
    colon: Token![:],
    ty: Type,
}

impl ToTokens for Type {
    fn to_tokens(&self, ts: &mut TokenStream2) {
        let additional_ts = match self {
            Type::Any(t) => quote_spanned!(t.span()=> crate::dispatch::TypeRepr::Any),
            Type::Unit(t) => quote_spanned!(t.span=> crate::dispatch::TypeRepr::Unit),
            Type::Int(t) => quote_spanned!(t.span()=> crate::dispatch::TypeRepr::Int),
            Type::String(t) => quote_spanned!(t.span()=> crate::dispatch::TypeRepr::String),
            Type::Named(path) => {
                quote_spanned!(path.span()=> <#path as crate::dispatch::Typed>::repr())
            }
            Type::Array(ArrayType { ty, .. }) => quote! {
                crate::dispatch::TypeRepr::Array(::std::boxed::Box::new(#ty))
            },
            Type::Enum(_, vars) => {
                let vars: Vec<_> = vars.vs.iter().map(|v| {
                    let name = v.name.to_string();
                    match &v.ty {
                        Some(t) => {
                            quote!(::std::borrow::ToOwned::to_owned(#name) => ::std::option::Option::Some(#t))
                        }
                        None => quote!(::std::borrow::ToOwned::to_owned(#name) => ::std::option::Option::None),
                    }
                }).collect();

                quote! {
                    crate::dispatch::TypeRepr::Enum(::maplit::hashmap!(
                        #( #vars, )*
                    ))
                }
            }
            Type::Struct(fields) => {
                let fs: Vec<_> = (fields.fs)
                    .iter()
                    .map(|f| {
                        let name = f.name.to_string();
                        let ty = &f.ty;
                        quote!(::std::borrow::ToOwned::to_owned(#name) => #ty)
                    })
                    .collect();

                quote! {
                    crate::dispatch::TypeRepr::Struct(::maplit::hashmap!(
                        #( #fs, )*
                    ))
                }
            }
            Type::Tuple(TupleType { tys, .. }) => {
                let tys = tys.into_iter().collect::<Vec<_>>();
                quote! {
                    crate::dispatch::TypeRepr::Tuple(
                        ::std::vec![ #( #tys, )* ]
                    )
                }
            }
        };

        ts.append_all(additional_ts);
    }
}

pub fn type_sig(input: TokenStream) -> TokenStream {
    #[derive(Parse)]
    struct Signature {
        input: Type,
        r_arrow: Option<Token![->]>,
        #[parse_if(r_arrow.is_some())]
        output: Option<Type>,
    }

    let sig = parse_macro_input!(input as Signature);
    let input_type = sig.input;

    let output_tokens = match sig.output {
        Some(t) => quote! {
            crate::dispatch::Signature {
                input: #input_type,
                output: ::std::option::Option::Some(#t),
            }
        },
        None => quote! {
            crate::dispatch::Signature {
                input: #input_type,
                output: ::std::option::Option::None,
            }
        },
    };

    output_tokens.into()
}

// Derive macro for `crate::dispatch::Typed`
pub fn derive_typed(item: TokenStream) -> TokenStream {
    use syn::Fields::{Named, Unit, Unnamed};

    let input = parse_macro_input!(item as DeriveInput);

    let fn_body = match input.data {
        Data::Enum(data) => enum_fn_body(data.variants),
        Data::Struct(data) => match data.fields {
            Unit => quote!(crate::dispatch::TypeRepr::Unit),
            Named(n) => named_fields_repr(n.named),
            Unnamed(u) => unnamed_fields_repr(u.unnamed),
        },
        Data::Union(_) => {
            return syn::Error::new(Span::call_site(), "cannot derive `Typed` for unions")
                .to_compile_error()
                .into();
        }
    };

    let generics = make_generics(&input.generics);
    let where_clause = input.generics.where_clause;
    let ty_name = input.ident;

    quote!(
        impl #generics crate::dispatch::Typed for #ty_name #where_clause {
            fn repr() -> crate::dispatch::TypeRepr {
                #fn_body
            }
        }
    )
    .into()
}

fn enum_fn_body(variants: impl IntoIterator<Item = syn::Variant>) -> TokenStream2 {
    let pairs: Vec<_> = variants
        .into_iter()
        .map(|v| {
            use syn::Fields::{Named, Unit, Unnamed};

            let name = v.ident.to_string();
            let ty = match v.fields {
                Unit => quote!(::std::option::Option::None),
                Named(n) => {
                    let t = named_fields_repr(n.named);
                    quote!(::std::option::Option::Some(#t))
                }
                Unnamed(u) => {
                    let t = unnamed_fields_repr(u.unnamed);
                    quote!(::std::option::Option::Some(#t))
                }
            };
            quote!(::std::borrow::ToOwned::to_owned(#name) => #ty)
        })
        .collect();

    quote! {
        crate::dispatch::TypeRepr::Enum(::maplit::hashmap!(#( #pairs, )*))
    }
}

fn named_fields_repr(fields: impl IntoIterator<Item = syn::Field>) -> TokenStream2 {
    let fs: Vec<_> = fields
        .into_iter()
        .map(|f| {
            let name = f.ident.expect("unexpected output from `syn`").to_string();
            let ty = f.ty;
            quote!(::std::borrow::ToOwned::to_owned(#name) => <#ty as crate::dispatch::Typed>::repr())
        })
        .collect();

    quote!(crate::dispatch::TypeRepr::Struct(
        ::maplit::hashmap!(#( #fs, )*)
    ))
}

fn unnamed_fields_repr(fields: impl IntoIterator<Item = syn::Field>) -> TokenStream2 {
    let mut fs: Vec<_> = fields
        .into_iter()
        .map(|f| {
            f.ident.expect_none("unexpected output from `syn`");
            let ty = f.ty;
            quote!(<#ty as crate::dispatch::Typed>::repr())
        })
        .collect();

    match fs.len() {
        0 => quote!(crate::dispatch::TypeRepr::Unit),
        1 => fs.remove(0),
        _ => quote!(crate::dispatch::TypeRepr::Tuple(::std::vec![#( #fs, )*])),
    }
}

fn make_generics(generics: &Generics) -> TokenStream2 {
    let params: Vec<_> = (generics.params)
        .iter()
        .map(|p| match p {
            syn::GenericParam::Type(t) => {
                let plus = match t.bounds.is_empty() {
                    true => TokenStream2::new(),
                    false => quote!(+),
                };
                let ident = &t.ident;
                let old_bounds = &t.bounds;

                quote! {
                    #ident: crate::dispatch::Typed #plus #old_bounds
                }
            }
            _ => p.into_token_stream(),
        })
        .collect();

    match params.as_slice() {
        [] => TokenStream2::new(),
        ps => quote!(< #( #ps ),* >),
    }
}

// Proc macro to implement `crate::dispatch::{Typed, TypedDeconstruct}` on a variety of core types
#[rustfmt::skip]
pub fn impl_core(input: TokenStream) -> TokenStream {
    #[derive(Parse)]
    struct Input {
        #[call(parse_repeated)]
        blocks: Vec<ImplBlock>,
    }

    #[derive(Parse)]
    struct ImplBlock {
        impl_token: Token![impl],
        generics: Generics,
        for_token: Token![for],
        self_ty: syn::Type,
        #[brace]
        brace: token::Brace,
        #[inside(brace)]
        content: Content,
    }

    #[derive(Parse)]
    struct Content {
        // @repr = <expr>;
        at_repr: AtKwd<kwd::repr>,
        repr_eq: Token![=],
        repr: Expr,
        repr_semi: Token![;],

        // @clone_with &self: { <expr> }
        at_clone: AtKwd<kwd::clone_with>,
        clone_amp: Token![&],
        clone_self: Token![self],
        clone_colon: Token![:],
        #[brace]
        clone_brace: token::Brace,
        #[inside(clone_brace)]
        clone_with: Expr,

        // fn $decon_name(&self) -> $decon_ty { $decon_body }
        decon_fn: Token![fn],
        decon_name: Ident,
        #[paren]
        decon_paren: token::Paren,
        #[inside(decon_paren)]
        decon_args: TokenStream2,
        decon_r_arrow: Token![->],
        decon_ty: syn::Type,
        #[brace]
        decon_brace: token::Brace,
        #[inside(decon_brace)]
        decon_body: TokenStream2,

        // fn $cons_name($cons_args) -> Self { $cons_body }
        cons_fn: Token![fn],
        cons_name: Ident,
        #[paren]
        cons_paren: token::Paren,
        #[inside(cons_paren)]
        cons_args: TokenStream2,
        cons_r_arrow: Token![->],
        cons_self: Token![Self],
        #[brace]
        cons_brace: token::Brace,
        #[inside(cons_brace)]
        cons_body: TokenStream2,
    }

    let input = parse_macro_input!(input as Input);

    input
        .blocks
        .into_iter()
        .map(|ImplBlock { generics, self_ty, content, .. }| {
            let Content {
                repr,
                at_clone, clone_amp, clone_self, clone_with,
                decon_name, decon_args, decon_ty, decon_body,
                cons_name, cons_args, cons_self, cons_body,
                ..
            } = content;

            // Wrapper spanned value to make error messages better
            let clone_value = quote_spanned!(at_clone.kwd.span()=> crate::dispatch::Value<'static>);

            quote! {
                impl#generics crate::dispatch::TypedDeconstruct for #self_ty {
                    fn get_repr(&self) -> crate::dispatch::TypeRepr {
                        <Self as crate::dispatch::Typed>::repr()
                    }
                    fn clone_into_value(#clone_amp #clone_self) -> #clone_value { #clone_with }
                    fn #decon_name(#decon_args) -> #decon_ty { #decon_body }
                }

                impl#generics crate::dispatch::Typed for #self_ty {
                    fn repr() -> crate::dispatch::TypeRepr { #repr }
                    fn #cons_name(#cons_args) -> #cons_self { #cons_body }
                }
            }
        })
        .collect::<TokenStream2>()
        .into()
}
