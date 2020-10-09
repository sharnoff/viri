//! Macros for defining named functions
//!
//! There's a more detailed explanation in the `config::named_fn` module in the main crate.
//! Documentation for the macros can be found where they are re-exported (in the `macros`
//! submodule).

use proc_macro::TokenStream;
use quote::{format_ident, quote, quote_spanned};
use syn::spanned::Spanned;
use syn::{parse_macro_input, FnArg, Ident, ItemFn, LitStr, Pat, PatType, ReturnType, Signature};

pub fn named(attr: TokenStream, item: TokenStream) -> TokenStream {
    let name = parse_macro_input!(attr as LitStr);
    let func = parse_macro_input!(item as ItemFn);

    if let Err(e) = check_signature(&func.sig) {
        let err = e.to_compile_error();
        return quote!(
            #err
            #func // we want to return the original function as well
        )
        .into();
    }

    let mut wrapper_arg_bindings = Vec::new();
    let mut convert_wrapper_args = Vec::new();
    let mut input_type_ids = Vec::new();
    let mut passthrough_args = Vec::new();

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

        convert_wrapper_args.push(quote! {
            let #wrapper_arg_name: #ty = *#wrapper_arg_name.downcast::<#ty>()
                .unwrap_or_else(|_| panic!("unexpected type provided as input"));
        });
        input_type_ids.push(quote_spanned! {
            ty.span()=>
            crate::config::Type::new::<#ty>()
        });
        passthrough_args.push(quote!( #wrapper_arg_name ));
        wrapper_arg_bindings.push(wrapper_arg_name);
    }

    let output_ty = match &func.sig.output {
        ReturnType::Default => quote!(()),
        ReturnType::Type(_arrow, ty) => quote!( #ty ),
    };

    let output_type_id = quote_spanned! {
        func.sig.output.span()=>
        crate::config::Type::new::<#output_ty>()
    };

    let base_fn_name = &func.sig.ident;
    let wrapper_name = format_ident!("__{}_named_wrapper", base_fn_name);

    // Handle whether the function is async
    let eval = match &func.sig.asyncness {
        None => quote! {
            // TODO: Typically, async functions will generate the future quickly, but take a
            // long(er) time to evaluate. This would give the opposite effect. Is that desired? The
            // alternative would be to wrap this in an async block without `.await`ing
            std::future::ready(
                Box::new(#base_fn_name( #( #passthrough_args, )* )) as
                    Box<dyn std::any::Any + Send + Sync>
            )
        },
        Some(_) => quote! {
            async move {
                Box::new(#base_fn_name( #( #passthrough_args, )* ).await) as
                    Box<dyn std::any::Any + Send + Sync>
            }
        },
    };

    let wrapper_fn = quote! {
        // All wrapper functions are async, but we need to phrase them without the syntax sugar
        // because we otherwise get a type mismatch - hence why we use `#[async_method]` here.
        #[viri_macros::async_method]
        async fn #wrapper_name( input_args: Vec<Box<dyn std::any::Any + Send + Sync>> )
                -> Box<dyn std::any::Any + Send + Sync> {
            use std::convert::TryInto;

            let args: Box<[Box<dyn std::any::Any + Send + Sync>; #required_num_args]>;
            args = input_args.into_boxed_slice().try_into()
                .unwrap_or_else(|args: Box<[_]>| panic!(
                    "unexpected number of arguments. expected {}, found {}",
                    #required_num_args,
                    args.len()
                ));

            let [#( #wrapper_arg_bindings, )*]: [Box<dyn std::any::Any + Send + Sync>; #required_num_args] = *args;

            #eval
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
