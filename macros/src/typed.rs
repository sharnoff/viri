//! Handling of extension handler type signatures

use derive_syn_parse::Parse;
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote, quote_spanned, ToTokens, TokenStreamExt};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{
    parse_macro_input, token, Data, DataEnum, DeriveInput, FieldsNamed, FieldsUnnamed, Generics,
    Ident, LitStr, Path, Token, WhereClause,
};

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
        #[prefix(Option<Token![->]> as r_arrow)]
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

// Derive macro for `crate::dispatch::Typed`: both `TypeConstruct` and `TypeDeconstruct`
pub fn manual_derive_typed(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);
    let input_span = input.span();

    let output = match input.data {
        Data::Union(_) => syn::Error::new(input_span, "#[derive(Typed)] cannot be used on unions")
            .into_compile_error(),
        Data::Enum(e) => derive_enum(input.ident, input.generics, e),
        Data::Struct(s) => match s.fields {
            syn::Fields::Unnamed(f) => derive_tuple(input.ident, input.generics, f),
            syn::Fields::Named(f) => derive_struct(input.ident, input.generics, f),
            syn::Fields::Unit => derive_unit_struct(input.ident, input.generics),
        },
    };

    output.into()
}

// A bit of context to make things a little easier to read
struct DeriveContext<S> {
    typed_construct: S,
    typed_deconstruct: S,
    type_kind: S,
    value: S,
    result: S,
    ok: S,
    err: S,
    some: S,
    string: S,
    primitive_str: S,
    hashmap: S,
    into_iter: S,
    next: S,
    is_some: S,
    ok_or_else: S,
    as_str: S,
    clone: S,
    from: S,
    slice: S,
    bool: S,
    vec: S,
    send: S,
    sync: S,
}

fn derive_context() -> DeriveContext<TokenStream2> {
    DeriveContext {
        typed_construct: quote!(crate::dispatch::TypedConstruct),
        typed_deconstruct: quote!(crate::dispatch::TypedDeconstruct),
        type_kind: quote!(crate::dispatch::TypeKind),
        value: quote!(crate::dispatch::Value),
        result: quote!(::std::result::Result),
        ok: quote!(::std::result::Result::Ok),
        err: quote!(::std::result::Result::Err),
        some: quote!(::std::option::Option::Some),
        string: quote!(::std::string::String),
        primitive_str: quote!(::std::primitive::str),
        hashmap: quote!(::std::collections::HashMap),
        into_iter: quote!(::std::iter::IntoIterator::into_iter),
        next: quote!(::std::iter::Iterator::next),
        is_some: quote!(::std::option::Option::is_some),
        ok_or_else: quote!(::std::option::Option::ok_or_else),
        as_str: quote!(::std::string::String::as_str),
        clone: quote!(::std::clone::Clone),
        from: quote!(::std::convert::From),
        slice: quote!(<[_]>),
        bool: quote!(::std::primitive::bool),
        vec: quote!(::std::vec::Vec),
        send: quote!(::std::marker::Send),
        sync: quote!(::std::marker::Sync),
    }
}

fn derive_enum(ident: Ident, generics: Generics, data: DataEnum) -> TokenStream2 {
    #[rustfmt::skip]
    let DeriveContext {
        typed_construct, typed_deconstruct, type_kind, value, result, ok, err, string,
        primitive_str, hashmap, into_iter, next, is_some, ok_or_else, as_str, clone, from, slice,
        send, sync, ..
    } = derive_context();

    let mut unit_variants = Vec::new();
    let mut unit_variants_strs = Vec::new();
    let mut ambiguous_variants = Vec::new();
    let mut ambiguous_variants_strs = Vec::new();
    let mut empty_tuple_variants = Vec::new();
    let mut empty_tuple_variants_strs = Vec::new();
    let mut nonempty_variants = Vec::new();
    let mut nonempty_variants_strs = Vec::new();
    let mut nonempty_variants_no_ambiguous = Vec::new();
    let mut nonempty_variants_no_ambiguous_strs = Vec::new();

    // The inner types of tuple variants that could be represented as units
    let mut ambiguous_tys = Vec::new();

    // We can use a single set of fields for all nonempty variants; tuple fields can be pattern
    // matched as { 0: _, 1: _, .. }, just like structs.
    let mut variant_fields = <Vec<Vec<TokenStream2>>>::new();
    // Unique helper names for each field in the above
    let mut unique_field_names = <Vec<Vec<Ident>>>::new();
    // But those varants need to have separate types constructed for them in order for conversion
    // to be made easier.
    let mut variant_type_dfns = <Vec<TokenStream2>>::new();

    for variant in &data.variants {
        let ident = &variant.ident;
        let lit_str = LitStr::new(&ident.to_string(), ident.span());

        match &variant.fields {
            syn::Fields::Unnamed(FieldsUnnamed { unnamed: fs, .. }) => {
                // Depending on the length of the tuple, it may be that this is:
                //  a. Actually a "unit",
                //  b. Ambiguous, because the contained type could be a "unit",
                //  c. Unambiguous
                // So we need to handle these cases separately.
                if fs.len() == 0 {
                    empty_tuple_variants.push(ident);
                    empty_tuple_variants_strs.push(lit_str);
                    continue;
                } else if fs.len() == 1 {
                    ambiguous_variants.push(ident);
                    ambiguous_variants_strs.push(lit_str.clone());
                    ambiguous_tys.push(&fs[0].ty);
                } else {
                    nonempty_variants_no_ambiguous.push(ident);
                    nonempty_variants_no_ambiguous_strs.push(lit_str.clone());
                }

                // Note: reaching this point implies `fs.len() > 1`
                nonempty_variants.push(ident);
                nonempty_variants_strs.push(lit_str);

                let fields = (0..fs.len())
                    .map(|i| {
                        use proc_macro2::{Literal, TokenTree};

                        // We can't just `quote!(#i)`, because that'll generate `<#i>_usize`, which
                        // isn't valid for tuple fields. It's easiest for us to make the token
                        // stream manually here.
                        TokenTree::Literal(Literal::usize_unsuffixed(i)).into()
                    })
                    .collect();

                variant_fields.push(fields);
                unique_field_names.push(
                    (0..fs.len())
                        .map(|i| format_ident!("_field_{}", i))
                        .collect(),
                );

                // Because this is a tuple, the type definition needs a trailing semicolon
                let fields = &variant.fields;
                variant_type_dfns.push(quote!( #fields; ));
            }
            syn::Fields::Named(FieldsNamed { named: fs, .. }) => {
                nonempty_variants.push(ident);
                nonempty_variants_strs.push(lit_str.clone());
                nonempty_variants_no_ambiguous.push(ident);
                nonempty_variants_no_ambiguous_strs.push(lit_str);

                variant_fields.push(
                    fs.iter()
                        .map(|f| f.ident.as_ref().unwrap().to_token_stream())
                        .collect(),
                );
                unique_field_names.push(
                    (0..fs.len())
                        .map(|i| format_ident!("_field_{}", i))
                        .collect(),
                );

                // Because this is a struct, the type definition doesn't need a trailing semicolon
                variant_type_dfns.push(variant.fields.to_token_stream());
            }
            syn::Fields::Unit => {
                unit_variants.push(ident);
                unit_variants_strs.push(lit_str);
                continue;
            }
        }
    }

    // This is used in exactly one spot; the reason why is explained there.
    let variant_fields_cloned = variant_fields.clone();

    let (cons_where, decon_where) =
        where_clauses(generics.where_clause.as_ref(), &enum_types(&data));
    let generic_args = generic_args(&generics);

    let construct = quote! {
        impl #generics #typed_construct for #ident #generic_args
        #cons_where Self: 'static {
            const CONS_ORDER: [#type_kind] = [#type_kind::Struct, #type_kind::String];

            fn err_string() -> &'static #primitive_str {
                "expected an enum variant; either by name (string) or field-value (struct)"
            }

            fn from_string(s: #string) -> #result<Self, #string> {
                match s.as_str() {
                    #( #unit_variants_strs => #ok(Self::#unit_variants), )*
                    #( #empty_tuple_variants_strs => #ok(Self::#empty_tuple_variants(())), )*
                    #( v @ #ambiguous_variants_strs => {
                        let does_contain = #slice::contains(
                            &<#ambiguous_tys as #typed_construct>::CONS_ORDER,
                            #type_kind::Unit
                        );
                        if does_contain {
                            #ok(Self::#ambiguous_variants(
                                <#ambiguous_tys as #typed_construct>::from_unit()?
                            ))
                        } else {
                            #err(::std::format!("enum variant `{}` missing data", v))
                        }
                    },)*
                    #( v @ #nonempty_variants_no_ambiguous_strs )|* => {
                        #err(::std::format!("enum variant `{}` missing data", v))
                    },
                    v => #err("unexpected enum variant {:?}", v),
                }
            }

            fn from_struct(fields: #hashmap<#string, #value>) -> #result<Self, #string> {
                let mut iter = #into_iter(fields);
                let (field, value) = #ok_or_else(#next(&mut iter), || "expected a field")?;

                if #is_some(#next(&mut iter)) {
                    return #err("expected only one field to singify the enum variant");
                }

                match #as_str(&field) {
                    #( #unit_variants_strs => {
                        let _: () = #value::convert(value)?;
                        #ok(Self::#unit_variants)
                    },)*
                    #( #empty_tuple_variants_strs => {
                        let _: () = #value::convert(value)?;
                        #ok(Self::#empty_tuple_variants(()))
                    },)*
                    #( #nonempty_variants_strs => {
                        #[derive(crate::macros::Typed)]
                        struct __TypedType #variant_type_dfns

                        let base: __TypedType = #value::convert(value);

                        #ok(Self {
                            // Due to a limitation in `quote`, the same repeated item can't be
                            // present more than once inside a repetition. So we hvae
                            // `variant_fields_cloned` to deal with that.
                            #( #variant_fields: base.#variant_fields_cloned, )*
                        })
                    },)*
                    s => #err(::std::format!("unexpected enum variant {:?}", s)),
                }
            }
        }
    };

    let deconstruct = quote! {
        impl #generics #typed_deconstruct for #ident #generic_args
        #decon_where Self: 'static + #send + #sync + #clone {
            fn type_kind(&self) -> #type_kind {
                match self {
                    #( Self::#unit_variants )|* => #type_kind::String,

                    // Represent something like Result<T, ()>::Err as a unit variant, to account
                    // for generics
                    #( Self::#ambiguous_variants(a) => match #typed_deconstruct::type_kind(a) {
                        #type_kind::Unit => #type_kind::String,
                        _ => #type_kind::Struct,
                    })*

                    #( Self::#nonempty_variants_no_ambiguous { .. } => #type_kind::Struct, )*
                }
            }

            fn clone_into_value(&self) -> #value<'static> {
                #value::new(#clone::clone(self))
            }

            fn as_string(&self) -> #string {
                match self {
                    #( Self::#unit_variants => <#string as #from>::from(#unit_variants_strs),)*
                    #( Self::#nonempty_variants { .. } => {
                        <#string as #from>::from(#nonempty_variants_strs)
                    })*
                }
            }

            fn as_struct(&self) -> #hashmap<#string, #value> {
                match self {
                    #( Self::#unit_variants => ::maplit::hashmap! {
                        <#string as #from>::from(#unit_variants_strs) => #value::new(()),
                    },)*
                    #( Self::#nonempty_variants { #( #variant_fields: #unique_field_names, )* } => {
                        #[derive(crate::macros::Typed)]
                        struct __TypedType #variant_type_dfns

                        ::maplit::hashmap! {
                            <#string as #from>::from(#nonempty_variants_strs) => {
                                #value::new(__TypedType {
                                    #( #variant_fields: #unique_field_names, )*
                                })
                            }
                        }
                    },)*
                }
            }
        }
    };

    quote! {
        #construct
        #deconstruct
    }
}

fn derive_struct(ident: Ident, generics: Generics, fields: FieldsNamed) -> TokenStream2 {
    #[rustfmt::skip]
    let DeriveContext {
        typed_construct, typed_deconstruct, type_kind, value, result, ok, err, string,
        primitive_str, hashmap, clone, from, ok_or_else, some, next, send, sync, ..
    } = derive_context();

    let types: Vec<_> = fields.named.iter().map(|f| &f.ty).collect();
    let (cons_where, decon_where) = where_clauses(generics.where_clause.as_ref(), &types);

    let generic_args = generic_args(&generics);

    let mut field_names = Vec::new();
    let mut field_strs = Vec::new();

    for f in fields.named.iter() {
        let ident = f.ident.as_ref().unwrap();
        field_strs.push(LitStr::new(&ident.to_string(), ident.span()));
        field_names.push(ident);
    }

    let field_names_cloned = field_names.clone();

    quote! {
        impl #generics #typed_construct for #ident #generic_args
        #cons_where Self: 'static {
            const CONS_ORDER: [#type_kind] = [#type_kind::Struct];

            fn err_string() -> &'static #primitive_str { "expected a struct" }

            fn from_struct(mut fields: #hashmap<#string, #value>) -> #result<Self, #string> {
                let this = Self {
                    #(
                    #field_names: #ok_or_else(
                            #hashmap::remove(&mut fields),
                            ::std::format!("missing field `{}`", #field_names_cloned),
                        )?,
                    )*
                };

                if let #some((f, _)) = #next(&mut #hashmap::iter(&fields)) {
                    return #err(::std::format!("unexpected field {:?}", f));
                }

                #ok(this)
            }
        }

        impl #generics #typed_deconstruct for #ident #generic_args
        #decon_where Self: 'static + #send + #sync + #clone {
            fn type_kind(&self) -> #type_kind { #type_kind::Struct }
            fn clone_into_value(&self) -> #value<'static> {
                #value::new(#clone::clone(self))
            }

            fn as_struct(&self) -> #hashmap<#string, #value> {
                ::maplit::hashmap! {
                    #( <#string as #from>::from(#field_strs) => #value::from_ref(&self.#field_names), )*
                }
            }
        }
    }
}

fn derive_tuple(ident: Ident, generics: Generics, fields: FieldsUnnamed) -> TokenStream2 {
    let fields: Vec<_> = fields.unnamed.into_iter().collect();

    // We'll special case length 0 and 1. The rest of this function assumes that we're dealing with
    // tuples of length >= 2
    match fields.as_slice() {
        [] => return derive_unit_tuple(ident, generics),
        [one_field] => return derive_single_elem_tuple(ident, generics, one_field),
        _ => (),
    }

    #[rustfmt::skip]
    let DeriveContext {
        typed_construct, typed_deconstruct, type_kind, value, result, ok, err, string,
        primitive_str, vec, clone, slice, send, sync, ..
    } = derive_context();

    let fields_len = fields.len();

    let types: Vec<_> = fields.iter().map(|f| &f.ty).collect();
    let (cons_where, decon_where) = where_clauses(generics.where_clause.as_ref(), &types);
    let generic_args = generic_args(&generics);

    let err_str = format!("expected tuple (array) of length {}", fields_len);

    let elem_names: Vec<_> = (0..fields_len)
        .map(|i| format_ident!("_elem_{}", i))
        .collect();
    let elem_names_cloned = elem_names.clone();

    let indexes = (0..fields_len).map(|i| proc_macro2::Literal::usize_unsuffixed(i));

    quote! {
        impl #generics #typed_construct for #ident #generic_args
        #cons_where Self: 'static {
            const CONS_ORER: [#type_kind] = #type_kind::Array;

            fn err_string() -> &'static #primitive_str { #err_str }

            fn from_array(array: #vec<#value>) -> #result<Self, #string> {
                match array.as_slice() {
                    [#( #elem_names, )*] => #ok(Self( #( #value::convert::<#types>(#elem_names_cloned)?, )* )),
                    vs => #err(format!(
                        "expected tuple with {} elements, found {}",
                        #fields_len,
                        #slice::len(vs),
                    )),
                }
            }
        }

        impl #generics #typed_deconstruct for #ident #generic_args
        #decon_where Self: 'static + #send + #sync + #clone {
            fn type_kind(&self) -> #type_kind { #type_kind::Array }

            fn clone_into_value(&self) -> #value<'static> {
                #value::new(#clone::clone(self))
            }

            fn as_array(&self) -> #vec<#value> {
                ::std::vec![
                    #( #value::from_ref(&self.#indexes), )*
                ]
            }
        }
    }
}

// Single-element tuples are treated identically to the inner types they represent
fn derive_single_elem_tuple(ident: Ident, generics: Generics, field: &syn::Field) -> TokenStream2 {
    #[rustfmt::skip]
    let DeriveContext {
        typed_construct, typed_deconstruct, type_kind, value, result, ok, string,
        primitive_str, hashmap, bool, vec, send, sync, clone, ..
    } = derive_context();

    let ty = &field.ty;

    let (cons_where, decon_where) = where_clauses(generics.where_clause.as_ref(), &[ty]);
    let generic_args = generic_args(&generics);

    quote! {
        impl #generics #typed_construct for #ident #generic_args
        #cons_where Self: 'static {
            const CONS_ORDER: [#type_kind] = <#ty as #typed_construct>::CONS_ORDER;

            fn err_string() -> &'static #primitive_str {
                <#ty as #typed_construct>::err_string()
            }

            fn from_any(any: #value<'static>) -> #result<Self, #string> {
                #ok(Self(<#ty as #typed_construct>::from_any(any)?))
            }

            fn from_int(int: ::num_bigint::BigInt) -> #result<Self, #string> {
                #ok(Self(<#ty as #typed_construct>::from_int(int)?))
            }

            fn from_bool(b: #bool) -> #result<Self, #string> {
                #ok(Self(<#ty as #typed_construct>::from_bool(b)?))
            }

            fn from_string(s: #string) -> #result<Self, #string> {
                #ok(Self(<#ty as #typed_construct>::from_string(s)?))
            }

            fn from_struct(fs: #hashmap<#string, #value>) -> #result<Self, #string> {
                #ok(Self(<#ty as #typed_construct>::from_struct(fs)?))
            }

            fn from_array(a: #vec<#value>) -> #result<Self, #string> {
                #ok(Self(<#ty as #typed_construct>::from_array(a)?))
            }
        }

        impl #generics #typed_deconstruct for #ident
        #decon_where Self: 'static + #send + #sync + #clone {
            fn type_kind(&self) -> #type_kind { <#ty as #typed_deconstruct>::type_kind(&self.0) }
            fn clone_into_value(&self) -> #value<'static> {
                <#ty as #typed_deconstruct>::clone_into_value(&self.0)
            }

            fn as_int(&self) -> ::num_bigint::BigInt {
                <#ty as #typed_deconstruct>::as_int(&self.0)
            }

            fn as_bool(&self) -> #bool {
                <#ty as #typed_deconstruct>::as_bool(&self.0)
            }

            fn as_string(&self) -> #string {
                <#ty as #typed_deconstruct>::as_string(&self.0)
            }

            fn as_struct(&self) -> #hashmap<#string, #value> {
                <#ty as #typed_deconstruct>::as_struct(&self.0)
            }

            fn as_array(&self) -> #vec<#value> {
                <#ty as #typed_deconstruct>::as_array(&self.0)
            }
        }
    }
}

fn derive_unit_tuple(ident: Ident, generics: Generics) -> TokenStream2 {
    #[rustfmt::skip]
    let DeriveContext {
        typed_construct, typed_deconstruct, type_kind, value, result, string, primitive_str,
        hashmap, ok, err, slice, from, send, sync, clone, ..
    } = derive_context();

    let vec = quote!(::std::vec::Vec);

    let (cons_where, decon_where) = where_clauses(generics.where_clause.as_ref(), &[]);
    let generic_args = generic_args(&generics);

    quote! {
        impl #generics #typed_construct for #ident #generic_args #cons_where Self: 'static {
            const CONS_ORDER: [#type_kind] = <() as #typed_construct>::CONS_ORDER;

            fn err_string() -> &'static #primitive_str {
                <() as #typed_construct>::err_string()
            }

            fn from_unit() -> #result<Self, #string> { #ok(Self()) }
            fn from_struct(fields: #hashmap<#string, #value>) -> #result<Self, #string> {
                match #hashmap::is_empty(&fields) {
                    true => #ok(Self()),
                    false => #err(<#string as #from>::from("expected an empty struct")),
                }
            }

            fn from_array(array: #vec<#value>) -> #result<Self, #string> {
                match #slice::is_empty(&array) {
                    true => #ok(Self()),
                    false => #err(<#string as #from>::from("expected an empty array")),
                }
            }
        }

        impl #generics #typed_deconstruct for #ident #generic_args
        #decon_where Self: 'static + #send + #sync + #clone {
            fn type_kind(&self) -> #type_kind { #type_kind::Unit }
            fn clone_into_value(&self) -> #value<'static> {
                #value::new(Self())
            }
        }
    }
}

fn derive_unit_struct(ident: Ident, generics: Generics) -> TokenStream2 {
    #[rustfmt::skip]
    let DeriveContext {
        typed_construct, typed_deconstruct, type_kind, value, result, ok, err, string,
        primitive_str, hashmap, from, send, sync, clone, ..
    } = derive_context();

    let (cons_where, decon_where) = where_clauses(generics.where_clause.as_ref(), &[]);
    let generic_args = generic_args(&generics);

    quote! {
        impl #generics #typed_construct for #ident #generic_args #cons_where Self: 'static {
            const CONS_ORDER: [#type_kind] = [#type_kind::Unit, #type_kind::Struct];

            fn err_string() -> &'static #primitive_str {
                "expected a unit value or an empty struct"
            }

            fn from_unit() -> #result<Self, #string> {
                #ok(Self)
            }

            fn from_struct(fields: #hashmap<#string, #value>) -> #result<Self, #string> {
                if !#hashmap::is_empty(&fields) {
                    #err(<#string as #from>::from("expected an empty struct, found one with fields"))
                } else {
                    #ok(Self)
                }
            }
        }

        impl #generics #typed_deconstruct for #ident #generic_args
        #decon_where Self: 'static + #send + #sync + #clone {
            fn type_kind(&self) -> #type_kind { #type_kind::Unit }
            fn clone_into_value(&self) -> #value<'static> {
                #value::new(Self)
            }
        }
    }
}

fn generic_args(generics: &Generics) -> TokenStream2 {
    use syn::GenericParam::{Const, Lifetime, Type};

    let args: Vec<_> = generics
        .params
        .iter()
        .map(|p| match p {
            Type(t) => t.ident.to_token_stream(),
            Lifetime(l) => l.lifetime.to_token_stream(),
            Const(c) => c.ident.to_token_stream(),
        })
        .collect();

    quote!( <#( #args, )*> )
}

// Produces the 'where' clauses required for TypeConstruct and TypeDeconstruct
fn where_clauses<'a>(
    given: Option<&WhereClause>,
    types: &[&'a syn::Type],
) -> (TokenStream2, TokenStream2) {
    let cons_type_bounds: TokenStream2 = types
        .iter()
        .cloned()
        .map(|t| quote_spanned!(t.span()=> #t: crate::dispatch::TypedConstruct,))
        .flatten()
        .collect();

    let decon_type_bounds: TokenStream2 = types
        .iter()
        .cloned()
        .map(|t| quote_spanned!(t.span()=> #t: crate::dispatch::TypedDeconstruct,))
        .flatten()
        .collect();

    if let Some(where_clause) = given {
        if where_clause.predicates.is_empty() || where_clause.predicates.trailing_punct() {
            (
                quote!(#where_clause #cons_type_bounds),
                quote!(#where_clause #decon_type_bounds),
            )
        } else {
            (
                quote!(#where_clause, #cons_type_bounds),
                quote!(#where_clause, #decon_type_bounds),
            )
        }
    } else {
        (
            quote!(where #cons_type_bounds),
            quote!(where #decon_type_bounds),
        )
    }
}

// Produces all of the types individually represented within an enum
fn enum_types(data: &DataEnum) -> Vec<&syn::Type> {
    let mut types = Vec::new();

    for v in data.variants.iter() {
        let fs = match &v.fields {
            syn::Fields::Unit => continue,
            syn::Fields::Named(FieldsNamed { named: fs, .. })
            | syn::Fields::Unnamed(FieldsUnnamed { unnamed: fs, .. }) => fs,
        };

        fs.iter().for_each(|f| types.push(&f.ty));
    }

    types
}
