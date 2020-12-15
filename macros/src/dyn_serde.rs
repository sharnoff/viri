//! Provides the `#[derive(SerdeDynClone)]` macro

use derive_syn_parse::Parse;
use proc_macro::TokenStream;
use quote::ToTokens;
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{parse_macro_input, DeriveInput, Token, Type};

pub fn serde_dyn_clone(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);

    if !input.generics.params.is_empty() {
        return syn::Error::new(
            input.generics.span(),
            "`#[derive(SerdeDynClone)]` cannot be used on generic types",
        )
        .to_compile_error()
        .into();
    }

    submit_ty(input.ident)
}

fn submit_ty(ty: impl ToTokens) -> TokenStream {
    quote::quote_spanned! (
        ty.span()=>
        ::inventory::submit!(crate::any::RegisteredSerde {
            base_ty: crate::any::Type::new::<#ty>(),
            de_ptr: {
                fn __de<'a>(
                    de: crate::any::Deserializer<'a>,
                ) -> Result<Box<dyn crate::any::DynClone>, crate::any::DeserializerError> {
                    <#ty as serde::Deserialize>::deserialize(de)
                        .map(|v| <Box<#ty>>::new(v) as Box<dyn crate::any::DynClone>)
                }

                __de
            },
            ser_ptr: {
                type _S = crate::any::Serializer;

                fn __ser<'a>(
                    serializer: _S,
                    dyn_clone: &'a dyn crate::any::DynClone,
                ) -> Result<<_S as serde::Serializer>::Ok, <_S as serde::Serializer>::Error> {
                    let v = dyn_clone.as_any()
                        .downcast_ref::<#ty>()
                        .ok_or_else(|| format!("unexpected type: expected `{}`, found `{}`", crate::any::Type::new::<#ty>().name(), dyn_clone.base_type().name()))
                        .unwrap();
                    serde::Serialize::serialize(v, serializer)
                }

                __ser
            },
        });
    )
    .into()
}

#[derive(Parse)]
struct RegisterAllInput {
    #[parse_terminated(Type::parse)]
    types: Punctuated<Type, Token![,]>,
}

pub fn register_dyn_clone(input: TokenStream) -> TokenStream {
    let inp = parse_macro_input!(input as RegisterAllInput);

    inp.types.into_iter().map(submit_ty).flatten().collect()
}
