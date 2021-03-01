//! Macros for defining named functions
//!
//! There's a more detailed explanation in the `config::named_fn` module in the main crate.
//! Documentation for the macros can be found where they are re-exported (in the `macros`
//! submodule).

use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{format_ident, quote, quote_spanned};
use syn::spanned::Spanned;
use syn::{FnArg, Ident, ItemFn, LitStr, Pat, PatType, ReturnType, Signature, Type};

pub fn named(attr: TokenStream, item: TokenStream) -> TokenStream {
    named2(attr.into(), item.into()).into()
}

fn named2(attr: TokenStream2, item: TokenStream2) -> TokenStream2 {
    let name = parse_macro_input2!(attr as LitStr);
    let func = parse_macro_input2!(item as ItemFn);

    if let Err(e) = check_signature(&func.sig) {
        let err = e.to_compile_error();
        return quote!(
            #err
            #func // we want to return the original function as well
        )
        .into();
    }

    let mut wrapper_arg_bindings = Vec::new();
    let mut input_type_ids = Vec::new();
    let mut passthrough_args = Vec::new();
    let mut downcast_args = Vec::new();

    let required_num_args = func.sig.inputs.len();

    for (i, arg) in func.sig.inputs.iter().enumerate() {
        let PatType { pat, ty, .. } = match arg {
            FnArg::Typed(pat_ty) => pat_ty,
            // This should have already been handled by `check_signature`
            FnArg::Receiver(_) => panic!("unexpected receiver argument"),
        };

        let wrapper_arg_name = try_extract_name(&pat).unwrap_or_else(|| {
            let name = format!("__arg_{}", i);
            Ident::new(&name, pat.span())
        });

        input_type_ids.push(quote_spanned! {
            ty.span()=>
            crate::any::Type::new::<#ty>()
        });
        passthrough_args.push(quote!( #wrapper_arg_name ));
        downcast_args.push(quote! {
            let #wrapper_arg_name = #wrapper_arg_name.try_downcast()
                .map_err(|err| format!("unexpected type for argument {}: {}", #i, err))
                .unwrap();
        });
        wrapper_arg_bindings.push(wrapper_arg_name);
    }

    let output_ty = match &func.sig.output {
        ReturnType::Default => quote!(()),
        ReturnType::Type(_arrow, ty) => quote!( #ty ),
    };

    let output_type_id = quote_spanned! {
        func.sig.output.span()=>
        crate::any::Type::new::<#output_ty>()
    };

    let base_fn_name = &func.sig.ident;
    let wrapper_name = format_ident!("__{}_named_wrapper", base_fn_name);

    let maybe_await = match &func.sig.asyncness {
        None => quote!(),
        Some(_) => quote!(.await),
    };

    let wrapper_fn = quote! {
        // All wrapper functions are async, but we need to phrase them without the syntax sugar
        // because we otherwise get a type mismatch - hence why we use `#[async_method]` here.
        #[viri_macros::async_method]
        async fn #wrapper_name( input_args: Vec<crate::any::BoxedAny> )
                -> crate::any::BoxedAny {
            use std::convert::TryInto;

            let args: Box<[crate::any::BoxedAny; #required_num_args]>;
            args = input_args.into_boxed_slice().try_into()
                .unwrap_or_else(|args: Box<[_]>| panic!(
                    "unexpected number of arguments. expected {}, found {}",
                    #required_num_args,
                    args.len()
                ));

            let [#( #wrapper_arg_bindings, )*] = *args;

            #( #downcast_args )*

            crate::any::BoxedAny::new(#base_fn_name( #( #passthrough_args, )* ) #maybe_await)
        }
    };

    let inventory = quote_spanned! {
        name.span()=>
        ::inventory::submit!(crate::config::named_fn::RegisteredFunction::new(
            #name,
            vec![#( #input_type_ids, )*],
            #output_type_id,
            #wrapper_name,
        ));
    };

    quote!(
        #func
        #wrapper_fn
        #inventory
    )
    .into()
}

// All the information about a single function we're going to register
struct Sig {
    args: Vec<(Ident, Type)>,
    output_ty: TokenStream2,
    // A tokenstream that can be expanded to
    base_fn_caller: TokenStream2,
    wrapper_name: Ident,
    is_async: bool,
    general_span: Span,
    registered_name: String,
}

impl Sig {
    fn register(&self) -> TokenStream2 {
        let mut arg_names = Vec::new();
        let mut input_type_ids = Vec::new();
        let mut downcast_args = Vec::new();

        let required_num_args = self.args.len();

        for (i, (arg_name, arg_ty)) in self.args.iter().enumerate() {
            input_type_ids.push(quote_spanned! {
                arg_ty.span()=>
                crate::any::Type::new::<#arg_ty>()
            });
            arg_names.push(arg_name);
            downcast_args.push(quote! {
                let #arg_name = #arg_name.try_downcast()
                    .map_err(|err| format!("unexpected type for argument {}: {}", #i, err))
                    .unwrap();
            });
        }

        let output_ty = &self.output_ty;
        let output_type_id = quote!(crate::any::Type::new::<#output_ty>());
        let wrapper_name = &self.wrapper_name;
        let base_fn_caller = &self.base_fn_caller;

        let maybe_await = match self.is_async {
            false => TokenStream2::new(),
            true => quote!(.await),
        };

        let wrapper_fn = quote! {
            // All wrapper functions are async, but we need to phrase them without the syntax sugar
            // because we otherwise get a type mismatch - hence why we use `#[async_method]` here.
            #[viri_macros::async_method]
            async fn #wrapper_name( input_args: Vec<crate::any::BoxedAny> )
                    -> crate::any::BoxedAny {
                use std::convert::TryInto;

                let args: Box<[crate::any::BoxedAny; #required_num_args]>;
                args = input_args.into_boxed_slice().try_into()
                    .unwrap_or_else(|args: Box<[_]>| panic!(
                        "unexpected number of arguments. expected {}, found {}",
                        #required_num_args,
                        args.len()
                    ));

                let [#( #arg_names, )*] = *args;

                #( #downcast_args )*

                crate::any::BoxedAny::new(#base_fn_caller( #( #arg_names, )* ) #maybe_await)
            }
        };

        let registered_name = &self.registered_name;

        let inventory = quote_spanned! {
            self.general_span.clone()=>
            ::inventory::submit!(crate::config::named_fn::RegisteredFunction::new(
                #registered_name,
                vec![#( #input_type_ids, )*],
                #output_type_id,
                #wrapper_name,
            ));
        };

        quote! {
            #wrapper_fn
            #inventory
        }
    }
}

/// Attempt to get a single bound name out of a pattern
///
/// This is a best-effort attempt, and the fallback is perfectly acceptible.
fn try_extract_name(pat: &Pat) -> Option<Ident> {
    match pat {
        Pat::Ident(pat_ident) => Some(pat_ident.ident.clone()),
        _ => None,
    }
}

fn check_signature(sig: &Signature) -> syn::Result<()> {
    // We have certain restrictions on what's allowed in one of these functions. We'll number
    // these, and then go through them each in turn.
    //  1. It must be free-standing (i.e. not a method)
    //  2. Must be safe
    //  3. Cannot have external ABI
    //  4. Cannot have generics
    //  5. Cannot be variadic

    // 1.
    if let Some(arg) = sig.receiver() {
        return Err(syn::Error::new(
            arg.span(),
            "named functions must be free-standing",
        ));
    }

    // 2.
    if let Some(unsafe_token) = sig.unsafety.as_ref() {
        return Err(syn::Error::new(
            unsafe_token.span(),
            "named functions cannot be unsafe",
        ));
    }

    // 3.
    if let Some(abi) = sig.abi.as_ref() {
        return Err(syn::Error::new(
            abi.span(),
            "named functions cannot specify an ABI",
        ));
    }

    // 4.
    if !sig.generics.params.is_empty() || sig.generics.where_clause.is_some() {
        return Err(syn::Error::new(
            sig.generics.span(),
            "named functions cannot use generics",
        ));
    }

    // 5.
    if let Some(var) = sig.variadic.as_ref() {
        return Err(syn::Error::new(
            var.span(),
            "named functions cannot use variadics",
        ));
    }

    Ok(())
}

// Our tests here are mostly to check that the output is correct in
#[cfg(test)]
mod tests {
    use super::named2;

    test_macro! {
        @name: single_arg_synchronous,
        named2!("my-foo") {
            fn foo(x: i32) -> i32 {
                2*x + 3
            }
        } => {
            fn foo(x: i32) -> i32 {
                2*x + 3
            }

            #[viri_macros::async_method]
            async fn __foo_named_wrapper(
                input_args: Vec<crate::any::BoxedAny>
            ) -> crate::any::BoxedAny {
                use std::convert::TryInto;

                let args: Box<[crate::any::BoxedAny; 1usize]>;
                args = input_args.into_boxed_slice().try_into()
                    .unwrap_or_else(|args: Box<[_]>| panic!(
                        "unexpected number of arguments. expected {}, found {}",
                        1usize,
                        args.len()
                    ));

                let [x,] = *args;

                let x = x.try_downcast()
                    .map_err(|err| format!("unexpected type for argument {}: {}", 0usize, err))
                    .unwrap();

                crate::any::BoxedAny::new(foo(x,))
            }

            ::inventory::submit!(crate::config::named_fn::RegisteredFunction::new(
                "my-foo",
                vec![crate::any::Type::new::<i32>(),],
                crate::any::Type::new::<i32>(),
                __foo_named_wrapper,
            ));
        }
    }

    test_macro! {
        @name: multi_args_async,
        named2!("my-foo") {
            #[other_attr]
            async fn foo(x: i32, y: bool, z: i32) -> i32 {
                match y { true => x, false => z }
            }
        } => {
            #[other_attr]
            async fn foo(x: i32, y: bool, z: i32) -> i32 {
                match y { true => x, false => z }
            }

            #[viri_macros::async_method]
            async fn __foo_named_wrapper(
                input_args: Vec<crate::any::BoxedAny>
            ) -> crate::any::BoxedAny {
                use std::convert::TryInto;

                let args: Box<[crate::any::BoxedAny; 3usize]>;
                args = input_args.into_boxed_slice().try_into()
                    .unwrap_or_else(|args: Box<[_]>| panic!(
                        "unexpected number of arguments. expected {}, found {}",
                        3usize,
                        args.len()
                    ));

                let [x, y, z,] = *args;

                let x = x.try_downcast()
                    .map_err(|err| format!("unexpected type for argument {}: {}", 0usize, err))
                    .unwrap();

                let y = y.try_downcast()
                    .map_err(|err| format!("unexpected type for argument {}: {}", 1usize, err))
                    .unwrap();

                let z = z.try_downcast()
                    .map_err(|err| format!("unexpected type for argument {}: {}", 2usize, err))
                    .unwrap();

                crate::any::BoxedAny::new(foo(x,y,z,).await)
            }

            ::inventory::submit!(crate::config::named_fn::RegisteredFunction::new(
                "my-foo",
                vec![crate::any::Type::new::<i32>(),crate::any::Type::new::<bool>(),crate::any::Type::new::<i32>(),],
                crate::any::Type::new::<i32>(),
                __foo_named_wrapper,
            ));
        }
    }
}
