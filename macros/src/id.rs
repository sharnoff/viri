use derive_syn_parse::Parse;
use proc_macro::TokenStream;
use quote::{quote, quote_spanned};
use syn::punctuated::Punctuated;
use syn::{parse_macro_input, token, Attribute, Ident, Token, Type, Visibility};

// The input - something like:
//
//     pub struct FooId
//
// or
//
//     struct BarId in [Bar], [Baz]
#[derive(Parse)]
struct Input {
    #[call(Attribute::parse_outer)]
    attrs: Vec<Attribute>,
    vis: Visibility,
    _struct_token: Token![struct],
    ident: Ident,
    #[peek(Token![in])]
    tail: Option<InputTail>,
    // TODO: we should allow an optional trailing semicolon here. It requires changing the parsing
    // function used for Tail.slices
    _semi: Option<Token![;]>,
}

#[derive(Parse)]
struct InputTail {
    _in_kwd: Token![in],
    #[call(Punctuated::parse_separated_nonempty)]
    slices: Punctuated<Slice, Token![,]>,
}

#[derive(Parse)]
struct Slice {
    #[bracket]
    bracket: token::Bracket,
    #[inside(bracket)]
    ty: Type,
}

pub fn id(input: TokenStream) -> TokenStream {
    let inp = parse_macro_input!(input as Input);

    let vis = inp.vis;
    let ident = inp.ident;
    let attrs = inp.attrs;

    let base_span = ident.span();

    let type_def = quote_spanned! {
        base_span=>
        #( #attrs )*
        #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #vis struct #ident(usize);
    };

    let mut impl_index = Vec::new();

    if let Some(tail) = inp.tail {
        for slice in tail.slices.into_iter() {
            let span = slice.bracket.span;
            let ty = slice.ty;
            impl_index.push(quote_spanned! {
                span=>
                impl std::ops::Index<#ident> for [#ty] {
                    type Output = #ty;

                    fn index(&self, idx: #ident) -> &Self::Output {
                        &self[idx.0]
                    }
                }

                impl std::ops::IndexMut<#ident> for [#ty] {
                    fn index_mut(&mut self, idx: #ident) -> &mut Self::Output {
                        &mut self[idx.0]
                    }
                }
            });
        }
    }

    quote!(
        #type_def
        #( #impl_index )*
    )
    .into()
}
