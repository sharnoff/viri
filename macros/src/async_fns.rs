use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{quote, quote_spanned, ToTokens};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{parse_macro_input, Attribute, Block, Ident, Signature, Token, TypeBareFn, Visibility};

// Part of the output type
struct NewMethodSignature {
    constness: Option<Token![const]>,
    unsafety: Option<Token![unsafe]>,
    fn_token: Token![fn],
    ident: Ident,
    generics: syn::Generics,
    inputs: Punctuated<syn::FnArg, Token![,]>,
    output: TokenStream2,
}

struct MethodItem {
    attrs: Vec<Attribute>,
    vis: Visibility,
    defaultness: Option<Token![default]>,
    sig: Signature,
    default: Option<Block>,
    semi_token: Option<Token![;]>,
}

pub fn async_method(attr: TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return syn::Error::new(
            Span::call_site(),
            "the `#[async_method]` attribute takes no arguments",
        )
        .to_compile_error()
        .into();
    }

    let method = parse_macro_input!(item as MethodItem);
    let MethodItem {
        attrs,
        vis,
        defaultness,
        sig,
        default,
        semi_token,
    } = method;

    // First, check a few things about the signature - notably including at
    let new_sig = match check_signature(sig) {
        Ok(sig) => sig,
        Err(e) => return e.to_compile_error().into(),
    };

    let new_body = new_method_body(default, semi_token);

    quote!(
        #( #attrs )*
        #vis #defaultness #new_sig #new_body
    )
    .into()
}

fn check_signature(sig: Signature) -> syn::Result<NewMethodSignature> {
    let sig_span = sig.span();

    let Signature {
        constness,
        asyncness,
        unsafety,
        abi,
        fn_token,
        ident,
        generics,
        paren_token: _,
        inputs,
        variadic,
        output,
    } = sig;

    if asyncness.is_none() {
        return Err(syn::Error::new(sig_span, "methods must be marked `async`"));
    };

    if let Some(abi) = abi {
        return Err(syn::Error::new(
            abi.span(),
            "attribute cannot be applied to functions with a specified ABI",
        ));
    } else if let Some(variadic) = variadic {
        return Err(syn::Error::new(
            variadic.span(),
            "attribute cannot be applied to functions with variadic arguments",
        ));
    }

    let has_reference = inputs.iter().any(HasRef::has_ref);
    let output = make_output_type(has_reference, output);

    Ok(NewMethodSignature {
        constness,
        unsafety,
        fn_token,
        ident,
        generics,
        inputs,
        output,
    })
}

// one of the two arguments will always be provided - never both or neither
fn new_method_body(default: Option<Block>, semi_token: Option<Token![;]>) -> TokenStream2 {
    if let Some(semi) = semi_token {
        return quote!( #semi );
    }

    let block = default.expect("method had neither function body nor semicolon");

    quote_spanned! {
        block.span()=>
        { std::boxed::Box::pin(async move #block) }
    }
}

pub fn async_fn(input: TokenStream) -> TokenStream {
    let ty = parse_macro_input!(input as TypeBareFn);

    let TypeBareFn {
        lifetimes,
        unsafety,
        abi,
        fn_token,
        paren_token: _,
        inputs,
        variadic,
        output,
    } = ty;

    // A lot of the work here looks similar to `check_signature`, because that's essentially the
    // entirety of this function.
    macro_rules! return_error {
        ($span:expr, $msg:expr $(,)?) => {{
            return syn::Error::new($span, $msg).to_compile_error().into();
        }};
    }

    if let Some(abi) = abi {
        return_error!(
            abi.span(),
            "this macro does not support functions with external ABIs",
        );
    } else if let Some(variadic) = variadic {
        return_error!(
            variadic.span(),
            "this macro does not support functions with variadic arguments",
        );
    }

    let has_ref = lifetimes.is_some() || inputs.iter().any(|arg| arg.ty.has_ref());
    let new_output = make_output_type(has_ref, output);

    quote!(
        #lifetimes #unsafety #abi #fn_token ( #inputs ) -> #new_output
    )
    .into()
}

fn make_output_type(has_reference: bool, output: syn::ReturnType) -> TokenStream2 {
    use syn::ReturnType::{Default, Type};

    match output {
        Default => wrap_future(has_reference, quote! { () }),
        Type(_arrow, ty) => wrap_future(has_reference, ty),
    }
}

fn wrap_future(has_reference: bool, ty: impl ToTokens) -> TokenStream2 {
    let maybe_lifetime = match has_reference {
        true => quote!( + '_ ),
        false => quote!(),
    };

    quote_spanned! {
        ty.span()=>
        std::pin::Pin<std::boxed::Box<dyn std::future::Future<Output=#ty> + Send + Sync #maybe_lifetime>>
    }
}

///////////////////////////////////////
// Boilerplate trait implementations //
///////////////////////////////////////

// A trait for whether an AST type contains a reference - used for determining whether the returned
// future should additionally be given a `+ '_`
trait HasRef {
    fn has_ref(&self) -> bool;
}

impl HasRef for syn::FnArg {
    fn has_ref(&self) -> bool {
        use syn::FnArg::{Receiver, Typed};
        use syn::PatType;

        match self {
            Receiver(recv) => recv.reference.is_some(),
            Typed(PatType { ty, .. }) => ty.has_ref(),
        }
    }
}

impl HasRef for syn::Type {
    fn has_ref(&self) -> bool {
        use syn::Type::*;
        use syn::TypeParamBound;

        match self {
            Array(arr) => arr.elem.has_ref(),
            BareFn(_) => false,
            Group(group) => group.elem.has_ref(),
            ImplTrait(impl_trait) => impl_trait.bounds.iter().any(|bound| match bound {
                TypeParamBound::Trait(_) => false,
                TypeParamBound::Lifetime(_) => true,
            }),
            Infer(_) => false, // We really can't tell for some of these :(
            Macro(_) => false,
            Never(_) => false, // <- But we know this one!
            Paren(ty) => ty.elem.has_ref(),
            Path(p) => p.path.has_ref(),
            Ptr(_) => false,
            Reference(_) => true,
            Slice(slice) => slice.elem.has_ref(),
            TraitObject(trait_obj) => trait_obj.bounds.iter().any(|bound| match bound {
                TypeParamBound::Trait(_) => false,
                TypeParamBound::Lifetime(_) => true,
            }),
            Tuple(tuple) => tuple.elems.iter().any(HasRef::has_ref),
            Verbatim(_) => false, // Can't tell for this one, either.

            // Hm... this should really use #[non_exhaustive] instead.
            __Nonexhaustive => false,
        }
    }
}

impl HasRef for syn::Path {
    fn has_ref(&self) -> bool {
        use syn::GenericArgument::{Binding, Const, Constraint, Lifetime, Type};
        use syn::PathArguments::{AngleBracketed, None, Parenthesized};

        let last_segment = self.segments.last().expect("empty path!");
        match &last_segment.arguments {
            AngleBracketed(generics) => generics.args.iter().any(|arg| match arg {
                Lifetime(_) => true,
                Type(ty) => ty.has_ref(),
                Binding(_) | Constraint(_) | Const(_) => false,
            }),
            Parenthesized(_) | None => false,
        }
    }
}

impl Parse for MethodItem {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let vis = input.parse()?;
        let defaultness = input.parse()?;
        let sig = input.parse()?;

        let semi_token = input.parse::<Option<Token![;]>>()?;
        let mut default = None;

        if semi_token.is_none() {
            default = Some(input.parse()?);
        }

        Ok(MethodItem {
            attrs,
            vis,
            defaultness,
            sig,
            semi_token,
            default,
        })
    }
}

impl ToTokens for NewMethodSignature {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        let NewMethodSignature {
            constness,
            unsafety,
            fn_token,
            ident,
            generics,
            inputs,
            output,
        } = self;

        // the implementation of `ToTokens` for `Generics` only prints the first set, not the where
        // clause
        let init_generics = generics;
        let where_clause = &generics.where_clause;

        let ts = quote! {
            #constness #unsafety #fn_token #ident #init_generics ( #inputs ) -> #output #where_clause
        };

        tokens.extend(ts);
    }
}
