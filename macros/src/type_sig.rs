//! Construction of extension handler type signatures

use derive_syn_parse::Parse;
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, quote_spanned, ToTokens, TokenStreamExt};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{parse_macro_input, token, Ident, Path, Token};

use super::AtKwd;

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
    #[prefix(Option<Token![:]> as colon)]
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
    #[prefix(Token![:])]
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
        #[prefix(Option<Token![=>]> as r_arrow)]
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
