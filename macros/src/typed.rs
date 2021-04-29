use proc_macro2::{Literal, Span, TokenStream};
use quote::{format_ident, quote, quote_spanned, ToTokens};
use syn::spanned::Spanned;
use syn::{
    Data, DataEnum, DeriveInput, Field, Fields, FieldsNamed, FieldsUnnamed, GenericParam, Generics,
    Ident, Index, LitStr, Type, Variant,
};

// Derive macro for `crate::dispatch::Typed`, including `TypeConstruct` and `TypeDeconstruct` as
// well
pub fn manual_derive_typed(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive_typed_impl(item.into()).into()
}

fn derive_typed_impl(item: TokenStream) -> TokenStream {
    let input = parse_macro_input2!(item as DeriveInput);
    let input_span = input.span();

    match input.data {
        Data::Union(_) => syn::Error::new(input_span, "#[derive(Typed)] cannot be used on unions")
            .into_compile_error(),
        Data::Enum(e) => derive_enum(input.ident, input.generics, e),
        Data::Struct(s) => match s.fields {
            Fields::Unnamed(f) => derive_tuple(input.ident, input.generics, f),
            Fields::Named(f) => derive_struct(input.ident, input.generics, f),
            Fields::Unit => derive_unit_struct(input.ident, input.generics),
        },
    }
}

// A bit of context to make things a little easier to read here. Formatting is intentionally
// skipped so that fields are a bit easier to read.
#[rustfmt::skip]
struct DeriveContext {
    typed:             TokenStream,
    typed_construct:   TokenStream,
    typed_deconstruct: TokenStream,
    type_kind:         TokenStream,
    type_repr:         TokenStream,
    value:             TokenStream,
    result:            TokenStream,
    crate_result:      TokenStream,
    error:             TokenStream,
    ok:                TokenStream,
    err:               TokenStream,
    some:              TokenStream,
    string:            TokenStream,
    primitive_str:     TokenStream,
    hashmap:           TokenStream,
    into_iter:         TokenStream,
    next:              TokenStream,
    is_some:           TokenStream,
    ok_or_else:        TokenStream,
    clone:             TokenStream,
    string_from:       TokenStream,
    slice:             TokenStream,
    bool:              TokenStream,
    vec:               TokenStream,
    send:              TokenStream,
    sync:              TokenStream,
}

fn derive_context() -> DeriveContext {
    DeriveContext {
        typed: quote!(crate::dispatch::Typed),
        typed_construct: quote!(crate::dispatch::TypedConstruct),
        typed_deconstruct: quote!(crate::dispatch::TypedDeconstruct),
        type_kind: quote!(crate::dispatch::TypeKind),
        type_repr: quote!(crate::dispatch::TypeRepr),
        value: quote!(crate::dispatch::Value),
        result: quote!(::std::result::Result),
        crate_result: quote!(crate::dispatch::typed::Result),
        error: quote!(crate::dispatch::typed::Error),
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
        clone: quote!(::std::clone::Clone),
        string_from: quote!(<::std::string::String as ::std::convert::From<_>>::from),
        // There really isn't a good way to refer to the slice primitive. It isn't in
        // `std::primitive`, so we need to just use the special syntax as it's given. We wrap it in
        // angle brackets to that #slice::foo works as expected.
        slice: quote!(<[_]>),
        bool: quote!(::std::primitive::bool),
        vec: quote!(::std::vec::Vec),
        send: quote!(::std::marker::Send),
        sync: quote!(::std::marker::Sync),
    }
}

// This struct is only used once, in `derive_enum(..)`. The description of each of the fields is
// primarily given there.
#[derive(Default)]
struct EnumCtx<'a> {
    unit_variants: Vec<&'a Ident>,
    unit_variants_strs: Vec<LitStr>,
    empty_tuple_variants: Vec<&'a Ident>,
    empty_tuple_variants_strs: Vec<LitStr>,
    nonempty_variants_no_ambiguous_strs: Vec<LitStr>,

    non_unit_variants: Vec<&'a Ident>,
    non_unit_variants_strs: Vec<LitStr>,
    non_unit_variants_no_ambiguous: Vec<&'a Ident>,

    single_elem_tuple_variants: Vec<&'a Ident>,
    single_elem_tuple_variants_strs: Vec<LitStr>,
    nonempty_tuple_variants: Vec<&'a Ident>,
    nonempty_tuple_variants_strs: Vec<LitStr>,
    nonempty_tuple_indexes: Vec<Vec<Index>>,
    nonempty_tuple_tys: Vec<Vec<&'a Type>>,
    nonempty_tuple_unique_names: Vec<Vec<Ident>>,
    nonempty_tuple_variants_len: Vec<Literal>,

    struct_variants: Vec<&'a Ident>,
    struct_variants_strs: Vec<LitStr>,
    struct_variants_fields: Vec<Vec<&'a Ident>>,
    struct_variants_fields_strs: Vec<Vec<LitStr>>,
    struct_variants_tys: Vec<Vec<&'a Type>>,

    ambiguous_tys: Vec<&'a Type>,
}

impl<'a> EnumCtx<'a> {
    fn new(variants: impl Iterator<Item = &'a Variant>) -> Self {
        let mut this = EnumCtx::default();

        for variant in variants {
            let ident = &variant.ident;
            let lit_str = LitStr::new(&ident.to_string(), ident.span());

            // There's a couple things that we need to do here. Mostly you'll just have to trust
            // that this is correct, because there's just *so* many fields that need to be properly
            // initialized.
            //
            // We'll start off by dealing with the "unit / non-unit" field options.
            match &variant.fields {
                Fields::Unnamed(_) | Fields::Named(_) => {
                    this.non_unit_variants.push(ident);
                    this.non_unit_variants_strs.push(lit_str.clone());
                }
                Fields::Unit => {
                    this.unit_variants.push(ident);
                    this.unit_variants_strs.push(lit_str.clone());
                }
            }

            // And then we'll do all of the other, more complicated stuff
            match &variant.fields {
                // Nothing left to do for unit variants
                Fields::Unit => (),

                // Tuple variants are a bit tricky. There's different cases for size 0, 1, and 2+.
                Fields::Unnamed(u) if u.unnamed.len() == 0 => {
                    this.empty_tuple_variants.push(ident);
                    this.empty_tuple_variants_strs.push(lit_str.clone());
                }
                Fields::Unnamed(u) if u.unnamed.len() == 1 => {
                    this.single_elem_tuple_variants.push(ident);
                    this.single_elem_tuple_variants_strs.push(lit_str.clone());
                    this.ambiguous_tys.push(&u.unnamed[0].ty);
                }
                Fields::Unnamed(FieldsUnnamed { unnamed: fs, .. }) => {
                    this.nonempty_tuple_variants.push(ident);
                    this.nonempty_tuple_variants_strs.push(lit_str.clone());
                    this.nonempty_variants_no_ambiguous_strs
                        .push(lit_str.clone());

                    // Write to `nonempty_tuple_{indexes,unique_names}`:
                    let call_site = Span::call_site();
                    let indexes = (0..fs.len() as u32)
                        .map(|i| Index {
                            index: i,
                            span: call_site.clone(),
                        })
                        .collect();

                    let names = (0..fs.len())
                        .map(|i| format_ident!("_field_{}", i))
                        .collect();

                    let tys = fs.iter().map(|f| &f.ty).collect();

                    this.nonempty_tuple_indexes.push(indexes);
                    this.nonempty_tuple_unique_names.push(names);
                    this.nonempty_tuple_variants_len
                        .push(Literal::usize_unsuffixed(fs.len()));
                    this.nonempty_tuple_tys.push(tys);
                }

                // Struct variants are thankfully fairly straightforward - there aren't any special
                // cases for handling units
                Fields::Named(FieldsNamed { named: fs, .. }) => {
                    this.struct_variants.push(ident);
                    this.struct_variants_strs.push(lit_str.clone());
                    this.nonempty_variants_no_ambiguous_strs
                        .push(lit_str.clone());
                    this.non_unit_variants_no_ambiguous.push(ident);

                    // Write to `struct_variants_fields{,strs}`:
                    let idents: Vec<_> = fs
                        .iter()
                        .map(|field| field.ident.as_ref().unwrap())
                        .collect();

                    let strs = idents
                        .iter()
                        .map(|id| LitStr::new(&id.to_string(), id.span()))
                        .collect();

                    let tys = fs.iter().map(|f| &f.ty).collect();

                    this.struct_variants_fields.push(idents);
                    this.struct_variants_fields_strs.push(strs);
                    this.struct_variants_tys.push(tys);
                }
            }
        }

        this
    }
}

fn derive_enum(ident: Ident, generics: Generics, data: DataEnum) -> TokenStream {
    #[rustfmt::skip]
    let DeriveContext {
        typed, typed_construct, typed_deconstruct, type_kind, type_repr, value, result,
        crate_result, error, ok, err, string, primitive_str, hashmap, into_iter, next, is_some,
        ok_or_else, clone, slice, send, sync, vec, some, string_from, ..
    } = derive_context();

    let ctx = EnumCtx::new(data.variants.iter());
    #[rustfmt::skip]
    let EnumCtx {
        // Unit variants are variants that use Fields::Unit -- i.e. stuff like
        //   enum Foo {
        //       Bar,
        //   }
        unit_variants, unit_variants_strs,
        // Empty tuples are like: Foo()
        empty_tuple_variants, empty_tuple_variants_strs,

        // Any struct varant, or any tuple variant with >= 2 elements
        nonempty_variants_no_ambiguous_strs,

        // "non-unit" variants are pretty much what it says on the label. Anything that's not a
        // unit. Edge-case examples of "non-unit" variants are:
        //   enum Foo {
        //       Bar(),
        //       Baz(()),
        //       Qux {},
        //   }
        non_unit_variants, non_unit_variants_strs,
        // "no_ambiguous" here removes the single-element tuples from the above set
        non_unit_variants_no_ambiguous,

        // These are fairly self explanatory
        single_elem_tuple_variants, single_elem_tuple_variants_strs,
        // Despite its name, "nonempty tuple variants" excludes tuple variants with only a single
        // element
        nonempty_tuple_variants, nonempty_tuple_variants_strs,
        // "nonempty tuple indexes/unique names" provide sets of indexes and names for each tuple
        // variant in the above set. "len" is just the number of elements in each "nonempty" tuple
        // variant.
        nonempty_tuple_indexes, nonempty_tuple_unique_names, nonempty_tuple_tys,
        nonempty_tuple_variants_len,

        // "struct variants" is what it says on the label
        struct_variants, struct_variants_strs,
        // "...fields" gives the list of field names *for each* variant in the above set
        struct_variants_fields, struct_variants_fields_strs, struct_variants_tys,

        // The inner type of single-element tuple variants
        ambiguous_tys,
    } = ctx;

    let ambiguous_tys_cloned = ambiguous_tys.clone();
    let nonempty_tuple_variants_cloned = nonempty_tuple_variants.clone();
    let struct_variants_cloned = struct_variants.clone();

    let original_where_clause = generics.where_clause.as_ref();

    let (cons_where, decon_where, typed_where) = where_clauses(&generics);
    let generic_args = generic_args(&generics);

    let typed = quote! {
        impl #generics #typed for #ident #generic_args
            #typed_where Self: #typed_deconstruct + #typed_construct
        {
            fn repr() -> #type_repr {
                #type_repr::Enum(::maplit::hashmap! {
                    // Unit
                    #( #string_from(#unit_variants_strs) => #type_repr::Unit, )*
                    #( #string_from(#empty_tuple_variants_strs) => #type_repr::Unit, )*

                    // Single-element tuples are simple. This also cleanly handles the ambiguous
                    // case.
                    #( #string_from(#single_elem_tuple_variants_strs) =>
                        <#ambiguous_tys as #typed>::repr(),
                    )*

                    // Multi-element tuples are fairly simple as well
                    #( #string_from(#nonempty_tuple_variants_strs) =>
                        #type_repr::Tuple(::std::vec![
                            #( <#nonempty_tuple_tys as #typed>::repr(), )*
                        ]),
                    )*

                    // And structs, too!
                    #( #string_from(#struct_variants_strs) =>
                        #type_repr::Struct(::maplit::hashmap! {
                            #( #string_from(#struct_variants_fields_strs) =>
                                <#struct_variants_tys as #typed>::repr(),
                            )*
                        }),
                    )*
                })
            }
        }
    };

    // We'd like our inner structs to be `struct _V`, but - on the offchance that the base struct
    // has that name (just to mess with us), we'll choose something different.
    let inner_struct_name = match ident.to_string().as_str() {
        "_V" => Ident::new("__V", Span::call_site()),
        _ => Ident::new("_V", Span::call_site()),
    };

    let construct = quote! {
        impl #generics #typed_construct for #ident #generic_args
            #cons_where Self: 'static + #send + #sync + #clone // TODO: do we need the clone bound?
        {
            fn cons_order() -> &'static [#type_kind] { &[#type_kind::Struct, #type_kind::String] }

            fn err_string() -> &'static #primitive_str {
                "expected an enum variant; either by name (string) or field-value (struct)"
            }

            fn from_string(s: #string) -> #crate_result<Self> {
                match #string::as_str(&s) {
                    #( #unit_variants_strs => #ok(Self::#unit_variants), )*
                    // Ambiguous variants *could* be a unit -- e.g. the `Err` variant of
                    // `Result<T, ()>`. If that's the case, we want this to be represented nicely,
                    // so that people could write the appropriate JSON as something like:
                    //   { result: "Err" }
                    // instead of:
                    //   { result: { "Err": [] } }
                    #( v @ #single_elem_tuple_variants_strs => {
                        let does_contain = #slice::contains(
                            <#ambiguous_tys as #typed_construct>::cons_order(),
                            &#type_kind::Unit,
                        );

                        if does_contain {
                            #ok(Self::#single_elem_tuple_variants(
                                <#ambiguous_tys_cloned as #typed_construct>::from_unit()
                            ))
                        } else {
                            #err(#error::from_str(::std::format!("enum variant `{}` missing data", v)))
                        }
                    },)*
                    #( v @ #nonempty_variants_no_ambiguous_strs =>
                        #err(#error::from_str(::std::format!("enum variant `{}` missing data", v))),
                    )*
                    v => #err(#error::from_str(::std::format!("unexpected enum variant {:?}", v))),
                }
            }

            fn from_struct(fields: #hashmap<#string, #value>) -> #crate_result<Self> {
                let mut iter = #into_iter(fields);

                let (field, value) = #ok_or_else(#next(&mut iter), || "expected a single field")?;

                if #is_some(&#next(&mut iter)) {
                    return #err(#error::from_str(
                        "expected only one field to signify the enum variant"
                    ));
                }

                let ctx_map = |e| #error::context(e, ::std::format!(".{}", field));

                match #string::as_str(&field) {
                    #( #unit_variants_strs => {
                        let _: () = #result::map_err(#value::convert(&value), ctx_map)?;
                        #ok(Self::#unit_variants)
                    },)*
                    #( #empty_tuple_variants_strs => {
                        let _: () = #result::map_err(#value::convert(&value), ctx_map)?;
                        #ok(Self::#empty_tuple_variants(()))
                    },)*
                    #( #single_elem_tuple_variants_strs =>
                        // Single-element tuples are equivalent to the values they contain
                        #ok(Self::#single_elem_tuple_variants(#result::map_err(
                            #value::convert(&value),
                            ctx_map
                        )?)),
                    )*
                    #( #nonempty_tuple_variants_strs => {
                        // Tuples with >1 elements are represented as arrays and only arrays.
                        let inner = #value::inner(&value);
                        let array = match #typed_deconstruct::type_kind(inner) {
                            #type_kind::Array => #typed_deconstruct::as_array(inner),
                            t => return #err(ctx_map(#error::from_str(::std::format!(
                                "expected an array type, found `{:?}`",
                                t,
                            )))),
                        };

                        match #vec::as_slice(&array) {
                            [ #( #nonempty_tuple_unique_names, )* ] => #ok(
                                Self::#nonempty_tuple_variants( #(
                                    #result::map_err(
                                        #value::convert(#nonempty_tuple_unique_names),
                                        |e| ctx_map(#error::context(
                                            e,
                                            ::std::format!(".{}", #nonempty_tuple_indexes),
                                        )),
                                    )?,
                                )* )
                            ),
                            vs => #err(ctx_map(#error::from_str(::std::format!(
                                "expected an array with {} elements, found {}",
                                #nonempty_tuple_variants_len,
                                #slice::len(vs),
                            )))),
                        }
                    }, )*
                    #( #struct_variants_strs => {
                        // All structs are required to be represented as such
                        let inner = #value::inner(&value);
                        let fields = match #typed_deconstruct::type_kind(inner) {
                            #type_kind::Struct => #typed_deconstruct::as_struct(inner),
                            t => return #err(ctx_map(#error::from_str(::std::format!(
                                "expected a struct type, found `{:?}`",
                                t,
                            )))),
                        };

                        let this = Self::#struct_variants {
                            #( #struct_variants_fields: {
                                let s = #struct_variants_fields_strs;
                                let val = #ok_or_else(
                                    #hashmap::remove(&mut fields, s),
                                    || ctx_map(#error::from_str(::std::format!("missing field `{}`", s))),
                                )?;

                                #result::map_err(
                                    #value::convert(&val),
                                    |e| ctx_map(#error::context(e, ::std::format!(".{}", s))),
                                )?
                            },)*
                        };

                        if let #some((f, _)) = #next(&mut #hashmap::iter(&fields)) {
                            return #err(ctx_map(#error::from_str(
                                ::std::format!("unexpected field {:?}", f)
                            )));
                        }

                        #ok(this)
                    },)*
                    unk => #err(#error::from_str(::std::format!("unknown enum variant {:?}", unk))),
                }
            }
        }
    };

    let deconstruct = quote! {
        impl #generics #typed_deconstruct for #ident #generic_args
            #decon_where Self: 'static + #send + #sync + #clone
        {
            fn type_kind(&self) -> #type_kind {
                match self {
                    #( Self::#unit_variants => #type_kind::String, )*
                    // Single-element tuple variants are ambiguous
                    #( Self::#single_elem_tuple_variants(a) => match #typed_deconstruct::type_kind(a) {
                        #type_kind::Unit => #type_kind::String,
                        _ => #type_kind::Struct,
                    }, )*
                    #( Self::#non_unit_variants_no_ambiguous { .. } => #type_kind::Struct, )*
                }
            }

            fn clone_into_value(&self) -> #value<'static> {
                #value::new(#clone::clone(self))
            }

            fn as_string(&self) -> #string {
                match self {
                    #( Self::#unit_variants => #string_from(#unit_variants_strs), )*
                    #( Self::#non_unit_variants { .. } => #string_from(#non_unit_variants_strs), )*
                }
            }

            fn as_struct(&self) -> #hashmap<#string, #value> {
                match self {
                    #( Self::#unit_variants => ::maplit::hashmap! {
                        #string_from(#unit_variants_strs) => #value::new(()),
                    },)*
                    #( Self::#empty_tuple_variants(()) => ::maplit::hashmap! {
                        #string_from(#empty_tuple_variants_strs) => #value::new(()),
                    },)*
                    #( Self::#single_elem_tuple_variants(v) => ::maplit::hashmap! {
                        #string_from(#single_elem_tuple_variants_strs) => #value::from_ref(v),
                    },)*
                    #( this @ Self::#nonempty_tuple_variants { .. } => {
                        #[repr(transparent)]
                        struct #inner_struct_name #generics #original_where_clause ( #ident #generics );

                        impl #generics #typed_deconstruct for #inner_struct_name #generic_args
                            #decon_where Self: 'static, #ident #generic_args: Clone
                        {
                            fn type_kind(&self) -> #type_kind { #type_kind::Array }

                            fn clone_into_value(&self) -> #value<'static> {
                                #value::new(Self( #clone::clone(&self.0) ))
                            }

                            fn as_array(&self) -> #vec<#value> {
                                match &self.0 {
                                    #ident::#nonempty_tuple_variants_cloned(
                                        #( #nonempty_tuple_unique_names, )*
                                    ) => {
                                        ::std::vec![ #(
                                            #value::from_ref(#nonempty_tuple_unique_names),
                                        )* ]
                                    }
                                    _ => ::std::unreachable!(),
                                }
                            }
                        }

                        // SAFETY: We know this is safe because the wrapper tuple is
                        // #[repr(transparent)]; it's really the only way we can produce a
                        // distinct, 'static type to the inner values.
                        let val: &#inner_struct_name #generic_args = unsafe {
                            ::std::mem::transmute(this)
                        };

                        ::maplit::hashmap! {
                            #string_from(#nonempty_tuple_variants_strs) => #value::from_ref(val),
                        }
                    },)*
                    #( this @ Self::#struct_variants { .. } => {
                        #[repr(transparent)]
                        struct #inner_struct_name #generics #original_where_clause ( #ident #generics );

                        impl #generics #typed_deconstruct for #inner_struct_name #generic_args
                            #decon_where Self: 'static, #ident #generic_args: Clone
                        {
                            fn type_kind(&self) -> #type_kind { #type_kind::Struct }

                            fn clone_into_value(&self) -> #value<'static> {
                                #value::new(Self( #clone::clone(&self.0) ))
                            }

                            fn as_struct(&self) -> #hashmap<#string, #value> {
                                match &self.0 {
                                    #ident::#struct_variants_cloned {
                                        #( #struct_variants_fields, )*
                                    } => {
                                        ::maplit::hashmap! { #(
                                            #string_from(#struct_variants_fields_strs) =>
                                                #value::from_ref(#struct_variants_fields),
                                        )* }
                                    }
                                    _ => ::std::unreachable!(),
                                }
                            }
                        }

                        // SAFETY: Same reasons as above
                        let val: &#inner_struct_name #generic_args = unsafe {
                            ::std::mem::transmute(this)
                        };

                        ::maplit::hashmap! {
                            #string_from(#struct_variants_strs) => #value::from_ref(val),
                        }
                    },)*
                }
            }
        }
    };

    quote! {
        #typed
        #construct
        #deconstruct
    }
}

fn derive_struct(ident: Ident, generics: Generics, fields: FieldsNamed) -> TokenStream {
    #[rustfmt::skip]
    let DeriveContext {
        typed, typed_construct, typed_deconstruct, type_kind, type_repr, value, result,
        crate_result, error, ok, err, string, primitive_str, hashmap, clone, ok_or_else, some,
        next, send, sync, string_from, ..
    } = derive_context();

    let field_types: Vec<_> = fields.named.iter().map(|f| &f.ty).collect();

    let (cons_where, decon_where, typed_where) = where_clauses(&generics);
    let generic_args = generic_args(&generics);

    let mut field_names = Vec::new();
    let mut field_strs = Vec::new();

    for f in fields.named.iter() {
        let ident = f.ident.as_ref().unwrap();
        field_strs.push(LitStr::new(&ident.to_string(), ident.span()));
        field_names.push(ident);
    }

    quote! {
        impl #generics #typed for #ident #generic_args
            #typed_where Self: #typed_deconstruct + #typed_deconstruct
        {
            fn repr() -> #type_repr {
                #type_repr::Struct(::maplit::hashmap! {
                    #( #string_from(#field_strs) => <#field_types as #typed>::repr(), )*
                })
            }
        }

        impl #generics #typed_construct for #ident #generic_args
            #cons_where Self: 'static
        {
            fn cons_order() -> &'static [#type_kind] { &[#type_kind::Struct] }

            fn err_string() -> &'static #primitive_str { "expected a struct" }

            fn from_struct(mut fields: #hashmap<#string, #value>) -> #crate_result<Self> {
                let this = Self {
                    #(
                    #field_names: {
                        let s = #field_strs;

                        let val = #ok_or_else(
                            #hashmap::remove(&mut fields, s),
                            || #error::from_str(::std::format!("missing field `{}`", s)),
                        )?;

                        #result::map_err(
                            #value::convert(&val),
                            |e| #error::context(e, ::std::format!(".{}", s)),
                        )?
                    },
                    )*
                };

                if let #some((f, _)) = #next(&mut #hashmap::iter(&fields)) {
                    return #err(#error::from_str(::std::format!("unexpected field {:?}", f)));
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
                    #( #string_from(#field_strs) => #value::from_ref(&self.#field_names), )*
                }
            }
        }
    }
}

fn derive_tuple(ident: Ident, generics: Generics, fields: FieldsUnnamed) -> TokenStream {
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
        typed, typed_construct, typed_deconstruct, type_kind, type_repr, value, result,
        crate_result, error, ok, err, primitive_str, vec, clone, slice, send, sync, ..
    } = derive_context();

    let fields_len = fields.len();

    let types: Vec<_> = fields.iter().map(|f| &f.ty).collect();
    let (cons_where, decon_where, typed_where) = where_clauses(&generics);
    let generic_args = generic_args(&generics);

    let err_str = format!("expected tuple (array) of length {}", fields_len);

    let elem_names: Vec<_> = (0..fields_len)
        .map(|i| format_ident!("_elem_{}", i))
        .collect();
    let elem_names_cloned = elem_names.clone();

    let indexes: Vec<_> = (0..fields_len)
        .map(|i| proc_macro2::Literal::usize_unsuffixed(i))
        .collect();

    quote! {
        impl #generics #typed for #ident #generic_args
            #typed_where Self: #typed_deconstruct + #typed_construct
        {
            fn repr() -> #type_repr {
                #type_repr::Tuple(::std::vec![
                    #( <#types as #typed>::repr(), )*
                ])
            }
        }

        impl #generics #typed_construct for #ident #generic_args
            #cons_where Self: 'static
        {
            fn cons_order() -> &'static [#type_kind] { &[#type_kind::Array] }

            fn err_string() -> &'static #primitive_str { #err_str }

            fn from_array(array: #vec<#value>) -> #crate_result<Self> {
                match array.as_slice() {
                    [#( #elem_names, )*] => {
                        #ok(Self( #( #result::map_err(
                            #value::convert::<#types>(#elem_names_cloned),
                            |e| #error::context(e, ::std::format!(".{}", #indexes)),
                        )? )* ))
                    }
                    vs => #err(#error::from_str(format!(
                        "expected tuple with {} elements, found {}",
                        #fields_len,
                        #slice::len(vs),
                    ))),
                }
            }
        }

        impl #generics #typed_deconstruct for #ident #generic_args
            #decon_where Self: 'static + #send + #sync + #clone
        {
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
fn derive_single_elem_tuple(ident: Ident, generics: Generics, field: &Field) -> TokenStream {
    #[rustfmt::skip]
    let DeriveContext {
        typed, typed_construct, typed_deconstruct, type_kind, type_repr, value, crate_result, ok,
        string, primitive_str, hashmap, bool, vec, send, sync, clone, ..
    } = derive_context();

    let ty = &field.ty;

    let (cons_where, decon_where, typed_where) = where_clauses(&generics);
    let generic_args = generic_args(&generics);

    quote! {
        impl #generics #typed for #ident #generic_args
            #typed_where Self: #typed_construct + #typed_deconstruct
        {
            fn repr() -> #type_repr {
                <#ty as #typed>::repr()
            }
        }

        impl #generics #typed_construct for #ident #generic_args
            #cons_where Self: 'static
        {
            fn cons_order() -> &'static [#type_kind] { <#ty as #typed_construct>::cons_order() }

            fn err_string() -> &'static #primitive_str {
                <#ty as #typed_construct>::err_string()
            }

            fn from_any(any: #value<'static>) -> #crate_result<Self> {
                #ok(Self(<#ty as #typed_construct>::from_any(any)?))
            }

            fn from_int(int: ::num_bigint::BigInt) -> #crate_result<Self> {
                #ok(Self(<#ty as #typed_construct>::from_int(int)?))
            }

            fn from_bool(b: #bool) -> #crate_result<Self> {
                #ok(Self(<#ty as #typed_construct>::from_bool(b)?))
            }

            fn from_string(s: #string) -> #crate_result<Self> {
                #ok(Self(<#ty as #typed_construct>::from_string(s)?))
            }

            fn from_unit() -> Self {
                Self(<#ty as #typed_construct>::from_unit())
            }

            fn from_struct(fs: #hashmap<#string, #value>) -> #crate_result<Self> {
                #ok(Self(<#ty as #typed_construct>::from_struct(fs)?))
            }

            fn from_array(a: #vec<#value>) -> #crate_result<Self> {
                #ok(Self(<#ty as #typed_construct>::from_array(a)?))
            }
        }

        impl #generics #typed_deconstruct for #ident
            #decon_where Self: 'static + #send + #sync + #clone
        {
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

fn derive_unit_tuple(ident: Ident, generics: Generics) -> TokenStream {
    #[rustfmt::skip]
    let DeriveContext {
        typed, typed_construct, typed_deconstruct, type_kind, type_repr, value, crate_result,
        error, string, primitive_str, hashmap, ok, err, slice, send, sync, clone, vec, ..
    } = derive_context();

    let (cons_where, decon_where, typed_where) = where_clauses(&generics);
    let generic_args = generic_args(&generics);

    quote! {
        impl #generics #typed for #ident #generic_args
            #typed_where Self: #typed_construct + #typed_deconstruct
        {
            fn repr() -> #type_repr { #type_repr::Unit }
        }

        impl #generics #typed_construct for #ident #generic_args
            #cons_where Self: 'static
        {
            fn cons_order() -> &'static [#type_kind] { <() as #typed_construct>::cons_order() }

            fn err_string() -> &'static #primitive_str {
                <() as #typed_construct>::err_string()
            }

            fn from_unit() -> Self { Self() }
            fn from_struct(fields: #hashmap<#string, #value>) -> #crate_result<Self> {
                match #hashmap::is_empty(&fields) {
                    true => #ok(Self()),
                    false => #err(#error::from_str("expected an empty struct")),
                }
            }

            fn from_array(array: #vec<#value>) -> #crate_result<Self> {
                match #slice::is_empty(&array) {
                    true => #ok(Self()),
                    false => #err(#error::from_str("expected an empty array")),
                }
            }
        }

        impl #generics #typed_deconstruct for #ident #generic_args
            #decon_where Self: 'static + #send + #sync + #clone
        {
            fn type_kind(&self) -> #type_kind { #type_kind::Unit }
            fn clone_into_value(&self) -> #value<'static> {
                #value::new(Self())
            }
        }
    }
}

fn derive_unit_struct(ident: Ident, generics: Generics) -> TokenStream {
    #[rustfmt::skip]
    let DeriveContext {
        typed, typed_construct, typed_deconstruct, type_kind, type_repr, value, crate_result,
        error, ok, err, string, primitive_str, hashmap, send, sync, clone, ..
    } = derive_context();

    let (cons_where, decon_where, typed_where) = where_clauses(&generics);
    let generic_args = generic_args(&generics);

    quote! {
        impl #generics #typed for #ident #generic_args
            #typed_where Self: #typed_construct + #typed_deconstruct
        {
            fn repr() -> #type_repr { #type_repr::Unit }
        }

        impl #generics #typed_construct for #ident #generic_args
            #cons_where Self: 'static
        {
            fn cons_order() -> &'static [#type_kind] { &[#type_kind::Unit, #type_kind::Struct] }

            fn err_string() -> &'static #primitive_str {
                "expected a unit value or an empty struct"
            }

            fn from_unit() -> Self { Self }

            fn from_struct(fields: #hashmap<#string, #value>) -> #crate_result<Self> {
                if !#hashmap::is_empty(&fields) {
                    #err(#error::from_str("expected an empty struct, found one with fields"))
                } else {
                    #ok(Self)
                }
            }
        }

        impl #generics #typed_deconstruct for #ident #generic_args
            #decon_where Self: 'static + #send + #sync + #clone
        {
            fn type_kind(&self) -> #type_kind { #type_kind::Unit }
            fn clone_into_value(&self) -> #value<'static> {
                #value::new(Self)
            }
        }
    }
}

fn generic_args(generics: &Generics) -> TokenStream {
    use syn::GenericParam::{Const, Lifetime, Type};

    if generics.params.is_empty() {
        return TokenStream::new();
    }

    let args: Vec<_> = generics
        .params
        .iter()
        .map(|p| match p {
            Type(t) => t.ident.to_token_stream(),
            Lifetime(l) => l.lifetime.to_token_stream(),
            Const(c) => c.ident.to_token_stream(),
        })
        .collect();

    quote!( <#( #args ),*> )
}

// Produces the 'where' clauses required for TypeConstruct, TypeDeconstruct, and Typed
fn where_clauses(generics: &Generics) -> (TokenStream, TokenStream, TokenStream) {
    let types: Vec<_> = generics
        .params
        .iter()
        .filter_map(|p| match p {
            GenericParam::Type(t) => Some(&t.ident),
            _ => None,
        })
        .collect();

    let cons_type_bounds: TokenStream = types
        .iter()
        .map(|t| quote_spanned!(t.span()=> #t: crate::dispatch::TypedConstruct,))
        .flatten()
        .collect();

    let decon_type_bounds: TokenStream = types
        .iter()
        .map(|t| quote_spanned!(t.span()=> #t: crate::dispatch::TypedDeconstruct,))
        .flatten()
        .collect();

    let typed_type_bounds: TokenStream = types
        .iter()
        .cloned()
        .map(|t| quote_spanned!(t.span()=> #t: crate::dispatch::Typed,))
        .flatten()
        .collect();

    // Handle possible missing/trailing commas or mising where clause altogether
    if let Some(where_clause) = generics.where_clause.as_ref() {
        if where_clause.predicates.is_empty() || where_clause.predicates.trailing_punct() {
            (
                quote!(#where_clause #cons_type_bounds),
                quote!(#where_clause #decon_type_bounds),
                quote!(#where_clause #typed_type_bounds),
            )
        } else {
            (
                quote!(#where_clause, #cons_type_bounds),
                quote!(#where_clause, #decon_type_bounds),
                quote!(#where_clause, #typed_type_bounds),
            )
        }
    } else {
        (
            quote!(where #cons_type_bounds),
            quote!(where #decon_type_bounds),
            quote!(where #typed_type_bounds),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::derive_typed_impl;

    test_macro! {
        @name: std_result,
        derive_typed_impl! {
            enum Result<T, E> {
                Ok(T),
                Err(E),
            }
        } => {
            impl<T, E> crate::dispatch::Typed for Result<T, E>
            where
                T: crate::dispatch::Typed,
                E: crate::dispatch::Typed,
                Self: crate::dispatch::TypedDeconstruct + crate::dispatch::TypedConstruct
            {
                fn repr() -> crate::dispatch::TypeRepr {
                    crate::dispatch::TypeRepr::Enum(::maplit::hashmap! {
                        <::std::string::String as ::std::convert::From<_>>::from("Ok") =>
                            <T as crate::dispatch::Typed>::repr(),
                        <::std::string::String as ::std::convert::From<_>>::from("Err") =>
                            <E as crate::dispatch::Typed>::repr(),
                    })
                }
            }

            impl<T, E> crate::dispatch::TypedConstruct for Result<T, E>
            where
                T: crate::dispatch::TypedConstruct,
                E: crate::dispatch::TypedConstruct,
                Self: 'static + ::std::marker::Send + ::std::marker::Sync + ::std::clone::Clone
            {
                fn cons_order() -> &'static [crate::dispatch::TypeKind] {
                    &[crate::dispatch::TypeKind::Struct, crate::dispatch::TypeKind::String]
                }

                fn err_string() -> &'static ::std::primitive::str {
                    "expected an enum variant; either by name (string) or field-value (struct)"
                }

                fn from_string(
                    s: ::std::string::String
                ) -> crate::dispatch::typed::Result<Self> {
                    match ::std::string::String::as_str(&s) {
                        v @ "Ok" => {
                            let does_contain = <[_]>::contains(
                                <T as crate::dispatch::TypedConstruct>::cons_order(),
                                &crate::dispatch::TypeKind::Unit,
                            );

                            if does_contain {
                                ::std::result::Result::Ok(Self::Ok(
                                    <T as crate::dispatch::TypedConstruct>::from_unit()
                                ))
                            } else {
                                ::std::result::Result::Err(crate::dispatch::typed::Error::from_str(
                                    ::std::format!("enum variant `{}` missing data", v)
                                ))
                            }
                        },
                        v @ "Err" => {
                            let does_contain = <[_]>::contains(
                                <E as crate::dispatch::TypedConstruct>::cons_order(),
                                &crate::dispatch::TypeKind::Unit,
                            );

                            if does_contain {
                                ::std::result::Result::Ok(Self::Err(
                                    <E as crate::dispatch::TypedConstruct>::from_unit()
                                ))
                            } else {
                                ::std::result::Result::Err(crate::dispatch::typed::Error::from_str(
                                    ::std::format!("enum variant `{}` missing data", v)
                                ))
                            }
                        },
                        v => ::std::result::Result::Err(crate::dispatch::typed::Error::from_str(
                            ::std::format!(
                                "unexpected enum variant {:?}",
                                v
                            )
                        )),
                    }
                }

                fn from_struct(
                    fields: ::std::collections::HashMap<::std::string::String, crate::dispatch::Value>
                ) -> crate::dispatch::typed::Result<Self> {
                    let mut iter = ::std::iter::IntoIterator::into_iter(fields);

                    let (field, value) = ::std::option::Option::ok_or_else(
                        ::std::iter::Iterator::next(&mut iter), || "expected a single field"
                    )?;

                    if ::std::option::Option::is_some(&::std::iter::Iterator::next(&mut iter)) {
                        return ::std::result::Result::Err(
                            crate::dispatch::typed::Error::from_str(
                                "expected only one field to signify the enum variant"
                            )
                        );
                    }

                    let ctx_map = |e| crate::dispatch::typed::Error::context(e, ::std::format!(".{}", field));

                    match ::std::string::String::as_str(&field) {
                        "Ok" => ::std::result::Result::Ok(Self::Ok(
                            ::std::result::Result::map_err(crate::dispatch::Value::convert(&value), ctx_map)?
                        )),
                        "Err" => ::std::result::Result::Ok(Self::Err(
                            ::std::result::Result::map_err(crate::dispatch::Value::convert(&value), ctx_map)?
                        )),
                        unk => ::std::result::Result::Err(crate::dispatch::typed::Error::from_str(
                            ::std::format!("unknown enum variant {:?}", unk)
                        )),
                    }
                }
            }

            impl<T, E> crate::dispatch::TypedDeconstruct for Result<T, E>
            where
                T: crate::dispatch::TypedDeconstruct,
                E: crate::dispatch::TypedDeconstruct,
                Self: 'static + ::std::marker::Send + ::std::marker::Sync + ::std::clone::Clone
            {
                fn type_kind(&self) -> crate::dispatch::TypeKind {
                    match self {
                        Self::Ok(a) => match crate::dispatch::TypedDeconstruct::type_kind(a) {
                            crate::dispatch::TypeKind::Unit => crate::dispatch::TypeKind::String,
                            _ => crate::dispatch::TypeKind::Struct,
                        },
                        Self::Err(a) => match crate::dispatch::TypedDeconstruct::type_kind(a) {
                            crate::dispatch::TypeKind::Unit => crate::dispatch::TypeKind::String,
                            _ => crate::dispatch::TypeKind::Struct,
                        },
                    }
                }

                fn clone_into_value(&self) -> crate::dispatch::Value<'static> {
                    crate::dispatch::Value::new(::std::clone::Clone::clone(self))
                }

                fn as_string(&self) -> ::std::string::String {
                    match self {
                        Self::Ok { .. } =>
                            <::std::string::String as ::std::convert::From<_>>::from("Ok"),
                        Self::Err { .. } =>
                            <::std::string::String as ::std::convert::From<_>>::from("Err"),
                    }
                }

                fn as_struct(
                    &self
                ) -> ::std::collections::HashMap<::std::string::String, crate::dispatch::Value> {
                    match self {
                        Self::Ok(v) => ::maplit::hashmap! {
                            <::std::string::String as ::std::convert::From<_>>::from("Ok") =>
                                crate::dispatch::Value::from_ref(v),
                        },
                        Self::Err(v) => ::maplit::hashmap! {
                            <::std::string::String as ::std::convert::From<_>>::from("Err") =>
                                crate::dispatch::Value::from_ref(v),
                        },
                    }
                }
            }
        }
    }

    test_macro! {
        @name: std_option,
        derive_typed_impl! {
            enum Option<T> {
                Some(T),
                None,
            }
        } => {
            impl<T> crate::dispatch::Typed for Option<T>
            where
                T: crate::dispatch::Typed,
                Self: crate::dispatch::TypedDeconstruct + crate::dispatch::TypedConstruct
            {
                fn repr() -> crate::dispatch::TypeRepr {
                    crate::dispatch::TypeRepr::Enum(::maplit::hashmap! {
                        <::std::string::String as ::std::convert::From<_>>::from("None") =>
                            crate::dispatch::TypeRepr::Unit,
                        <::std::string::String as ::std::convert::From<_>>::from("Some") =>
                            <T as crate::dispatch::Typed>::repr(),
                    })
                }
            }

            impl<T> crate::dispatch::TypedConstruct for Option<T>
            where
                T: crate::dispatch::TypedConstruct,
                Self: 'static + ::std::marker::Send + ::std::marker::Sync + ::std::clone::Clone
            {
                fn cons_order() -> &'static [crate::dispatch::TypeKind] {
                    &[crate::dispatch::TypeKind::Struct, crate::dispatch::TypeKind::String]
                }

                fn err_string() -> &'static ::std::primitive::str {
                    "expected an enum variant; either by name (string) or field-value (struct)"
                }

                fn from_string(
                    s: ::std::string::String
                ) -> crate::dispatch::typed::Result<Self> {
                    match ::std::string::String::as_str(&s) {
                        "None" => ::std::result::Result::Ok(Self::None),
                        v @ "Some" => {
                            let does_contain = <[_]>::contains(
                                <T as crate::dispatch::TypedConstruct>::cons_order(),
                                &crate::dispatch::TypeKind::Unit,
                            );

                            if does_contain {
                                ::std::result::Result::Ok(Self::Some(
                                    <T as crate::dispatch::TypedConstruct>::from_unit()
                                ))
                            } else {
                                ::std::result::Result::Err(crate::dispatch::typed::Error::from_str(
                                    ::std::format!("enum variant `{}` missing data", v)
                                ))
                            }
                        },
                        v => ::std::result::Result::Err(crate::dispatch::typed::Error::from_str(
                            ::std::format!("unexpected enum variant {:?}", v)
                        )),
                    }
                }

                fn from_struct(
                    fields: ::std::collections::HashMap<::std::string::String, crate::dispatch::Value>
                ) -> crate::dispatch::typed::Result<Self> {
                    let mut iter = ::std::iter::IntoIterator::into_iter(fields);

                    let (field, value) = ::std::option::Option::ok_or_else(
                        ::std::iter::Iterator::next(&mut iter),
                        || "expected a single field"
                    )?;

                    if ::std::option::Option::is_some(&::std::iter::Iterator::next(&mut iter)) {
                        return ::std::result::Result::Err(
                            crate::dispatch::typed::Error::from_str(
                                "expected only one field to signify the enum variant"
                            )
                        );
                    }

                    let ctx_map = |e| crate::dispatch::typed::Error::context(e, ::std::format!(".{}", field));

                    match ::std::string::String::as_str(&field) {
                        "None" => {
                            let _: () = ::std::result::Result::map_err(
                                crate::dispatch::Value::convert(&value),
                                ctx_map
                            )?;
                            ::std::result::Result::Ok(Self::None)
                        },
                        "Some" => ::std::result::Result::Ok(Self::Some(
                            ::std::result::Result::map_err(crate::dispatch::Value::convert(&value), ctx_map)?
                        )),
                        unk => ::std::result::Result::Err(crate::dispatch::typed::Error::from_str(
                            ::std::format!("unknown enum variant {:?}", unk)
                        )),
                    }
                }
            }

            impl<T> crate::dispatch::TypedDeconstruct for Option<T>
            where
                T: crate::dispatch::TypedDeconstruct,
                Self: 'static + ::std::marker::Send + ::std::marker::Sync + ::std::clone::Clone
            {
                fn type_kind(&self) -> crate::dispatch::TypeKind {
                    match self {
                        Self::None => crate::dispatch::TypeKind::String,
                        Self::Some(a) => match crate::dispatch::TypedDeconstruct::type_kind(a) {
                            crate::dispatch::TypeKind::Unit => crate::dispatch::TypeKind::String,
                            _ => crate::dispatch::TypeKind::Struct,
                        },
                    }
                }

                fn clone_into_value(&self) -> crate::dispatch::Value<'static> {
                    crate::dispatch::Value::new(::std::clone::Clone::clone(self))
                }

                fn as_string(&self) -> ::std::string::String {
                    match self {
                        Self::None =>
                            <::std::string::String as ::std::convert::From<_>>::from("None"),
                        Self::Some { .. } =>
                            <::std::string::String as ::std::convert::From<_>>::from("Some"),
                    }
                }

                fn as_struct(
                    &self
                ) -> ::std::collections::HashMap<::std::string::String, crate::dispatch::Value> {
                    match self {
                        Self::None => ::maplit::hashmap! {
                            <::std::string::String as ::std::convert::From<_>>::from("None") =>
                                crate::dispatch::Value::new(()),
                        },
                        Self::Some(v) => ::maplit::hashmap! {
                            <::std::string::String as ::std::convert::From<_>>::from("Some") =>
                                crate::dispatch::Value::from_ref(v),
                        },
                    }
                }
            }
        }
    }

    test_macro! {
        @name: complex_enum,
        derive_typed_impl! {
            enum Complex<T> {
                FirstUnit,
                SecondUnit,
                FirstAmbiguous(i32),
                SecondAmbiguous(String),
                ThreeTup(usize, T, T),
                FourTup(String, T, T, T),
                SmallStruct { x: u32, y: u32 },
                BigStruct { desc: String, vals: Vec<T>, id: usize, x: u32, y: u32 },
            }
        } => {
            impl<T> crate::dispatch::Typed for Complex<T>
            where
                T: crate::dispatch::Typed,
                Self: crate::dispatch::TypedDeconstruct + crate::dispatch::TypedConstruct
            {
                fn repr() -> crate::dispatch::TypeRepr {
                    crate::dispatch::TypeRepr::Enum(
                        ::maplit::hashmap! {
                            <::std::string::String as ::std::convert::From<_>>::from("FirstUnit") =>
                                crate::dispatch::TypeRepr::Unit,
                            <::std::string::String as ::std::convert::From<_>>::from("SecondUnit") =>
                                crate::dispatch::TypeRepr::Unit,
                            <::std::string::String as ::std::convert::From<_>>::from("FirstAmbiguous") =>
                                <i32 as crate::dispatch::Typed>::repr(),
                            <::std::string::String as ::std ::convert::From<_>>::from("SecondAmbiguous") =>
                                <String as crate::dispatch::Typed>::repr(),
                            <::std::string::String as ::std::convert::From<_>>::from("ThreeTup") =>
                                crate::dispatch::TypeRepr::Tuple(::std::vec![
                                    <usize as crate::dispatch::Typed>::repr(),
                                    <T as crate::dispatch::Typed>::repr(),
                                    <T as crate::dispatch::Typed>::repr(),
                                ]),
                            <::std::string::String as ::std::convert::From<_>>::from("FourTup") =>
                                crate ::dispatch::TypeRepr::Tuple(::std::vec![
                                    <String as crate ::dispatch::Typed>::repr(),
                                    <T as crate::dispatch::Typed>::repr(),
                                    <T as crate::dispatch::Typed>::repr(),
                                    <T as crate::dispatch::Typed>::repr(),
                                ]),
                            <::std::string::String as ::std::convert::From<_>>::from("SmallStruct") =>
                                crate::dispatch::TypeRepr::Struct(::maplit::hashmap! {
                                    <::std::string::String as ::std::convert::From<_>>::from("x") =>
                                        <u32 as crate::dispatch::Typed>::repr(),
                                    <::std::string::String as ::std::convert::From<_>>::from("y") =>
                                        <u32 as crate ::dispatch::Typed>::repr(),
                                }),
                            <::std::string::String as ::std::convert::From<_>>::from("BigStruct") =>
                                crate::dispatch::TypeRepr::Struct(::maplit::hashmap! {
                                    <::std::string::String as ::std::convert::From<_>>::from("desc") =>
                                        <String as crate::dispatch::Typed>::repr(),
                                    <::std::string::String as ::std::convert::From<_>>::from("vals") =>
                                        <Vec<T> as crate::dispatch::Typed>::repr(),
                                    <::std::string::String as ::std::convert::From<_>>::from("id") =>
                                        <usize as crate::dispatch::Typed>::repr(),
                                    <::std::string::String as ::std::convert::From<_>>::from("x") =>
                                        <u32 as crate::dispatch::Typed>::repr(),
                                    <::std::string::String as ::std::convert::From<_>>::from("y") =>
                                        <u32 as crate::dispatch::Typed>::repr(),
                                }),
                        }
                    )
                }
            }

            impl<T> crate::dispatch::TypedConstruct for Complex<T>
            where
                T: crate::dispatch::TypedConstruct,
                Self: 'static + ::std::marker::Send + ::std::marker::Sync + ::std::clone::Clone
            {
                fn cons_order() -> &'static [crate::dispatch::TypeKind] {
                    &[crate::dispatch::TypeKind::Struct, crate::dispatch::TypeKind::String]
                }

                fn err_string() -> &'static ::std::primitive::str {
                    "expected an enum variant; either by name (string) or field-value (struct)"
                }

                fn from_string(s: ::std::string::String) -> crate::dispatch::typed::Result<Self> {
                    match ::std::string::String::as_str(&s) {
                        "FirstUnit" => ::std::result::Result::Ok(Self::FirstUnit),
                        "SecondUnit" => ::std::result::Result::Ok(Self::SecondUnit),
                        v @ "FirstAmbiguous" => {
                            let does_contain = <[_]>::contains(
                                <i32 as crate::dispatch::TypedConstruct>::cons_order(),
                                &crate::dispatch::TypeKind::Unit,
                            );

                            if does_contain {
                                ::std::result::Result::Ok(Self::FirstAmbiguous(
                                    <i32 as crate::dispatch::TypedConstruct>::from_unit()
                                ))
                            } else {
                                ::std::result::Result::Err(crate::dispatch::typed::Error::from_str(
                                    ::std::format!("enum variant `{}` missing data", v)
                                ))
                            }
                        },
                        v @ "SecondAmbiguous" => {
                            let does_contain = <[_]>::contains(
                                <String as crate::dispatch::TypedConstruct>::cons_order(),
                                &crate::dispatch::TypeKind::Unit,
                            );

                            if does_contain {
                                ::std::result::Result::Ok(Self::SecondAmbiguous(
                                    <String as crate::dispatch::TypedConstruct>::from_unit()
                                ))
                            } else {
                                ::std::result::Result::Err(crate::dispatch::typed::Error::from_str(
                                    ::std::format!("enum variant `{}` missing data", v)
                                ))
                            }
                        },
                        v @ "ThreeTup" =>
                            ::std::result::Result::Err(crate::dispatch::typed::Error::from_str(
                                ::std::format!("enum variant `{}` missing data", v)
                            )),
                        v @ "FourTup" =>
                            ::std::result::Result::Err(crate::dispatch::typed::Error::from_str(
                                ::std::format!("enum variant `{}` missing data", v)
                            )),
                        v @ "SmallStruct" =>
                            ::std::result::Result::Err(crate::dispatch::typed::Error::from_str(::std::format!(
                                "enum variant `{}` missing data",
                                v
                            ))),
                        v @ "BigStruct" =>
                            ::std::result::Result::Err(crate::dispatch::typed::Error::from_str(
                                ::std::format!("enum variant `{}` missing data", v)
                            )),
                        v => ::std::result::Result::Err(crate::dispatch::typed::Error::from_str(
                            ::std::format!("unexpected enum variant {:?}", v)
                        )),
                    }
                }

                fn from_struct(
                    fields: ::std::collections::HashMap<::std::string::String, crate::dispatch::Value>
                ) -> crate::dispatch::typed::Result<Self> {
                    let mut iter = ::std::iter::IntoIterator::into_iter(fields);

                    let(field, value) = ::std::option::Option::ok_or_else(
                        ::std::iter::Iterator::next(&mut iter),
                        || "expected a single field"
                    )?;

                    if ::std::option::Option::is_some(&::std::iter::Iterator::next(&mut iter)) {
                        return ::std::result::Result::Err(crate::dispatch::typed::Error::from_str(
                            "expected only one field to signify the enum variant"
                        ));
                    }

                    let ctx_map = |e| crate::dispatch::typed::Error::context(e, ::std::format!(".{}", field));

                    match ::std::string::String::as_str(&field) {
                        "FirstUnit" => {
                            let _:() = ::std::result::Result::map_err(
                                crate::dispatch::Value::convert(&value),
                                ctx_map
                            )?;
                            ::std::result::Result::Ok(Self::FirstUnit)
                        },
                        "SecondUnit" => {
                            let _:() = ::std::result::Result::map_err(
                                crate::dispatch::Value::convert(&value),
                                ctx_map
                            )?;
                            ::std::result::Result::Ok(Self::SecondUnit)
                        },
                        "FirstAmbiguous" => ::std::result::Result::Ok(Self::FirstAmbiguous(
                            ::std::result::Result::map_err(crate::dispatch::Value::convert(&value), ctx_map)?
                        )),
                        "SecondAmbiguous" => ::std::result::Result::Ok(Self::SecondAmbiguous(
                            ::std::result::Result::map_err(crate::dispatch::Value::convert(&value), ctx_map)?
                        )),
                        "ThreeTup" => {
                            let inner = crate::dispatch::Value::inner(&value);

                            let array = match crate::dispatch::TypedDeconstruct::type_kind(inner) {
                                crate::dispatch::TypeKind::Array =>
                                    crate::dispatch::TypedDeconstruct::as_array(inner),
                                t => return ::std::result::Result::Err(ctx_map(
                                    crate::dispatch::typed::Error::from_str(::std::format!(
                                        "expected an array type, found `{:?}`",
                                        t,
                                    ))
                                )),
                            };

                            match ::std::vec::Vec::as_slice(&array) {
                                [_field_0, _field_1, _field_2,] =>
                                    ::std::result::Result::Ok(Self::ThreeTup(
                                        ::std::result::Result::map_err(
                                            crate::dispatch::Value::convert(_field_0),
                                            |e| ctx_map(crate::dispatch::typed::Error::context(
                                                e,
                                                ::std::format!(".{}", 0),
                                            )),
                                        )?,
                                        ::std::result::Result::map_err(
                                            crate::dispatch::Value::convert(_field_1),
                                            |e| ctx_map(crate::dispatch::typed::Error::context(
                                                e,
                                                ::std::format!(".{}", 1),
                                            )),
                                        )?,
                                        ::std::result::Result::map_err(
                                            crate::dispatch::Value::convert(_field_2),
                                            |e| ctx_map(crate::dispatch::typed::Error::context(
                                                e,
                                                ::std::format!(".{}", 2),
                                            )),
                                        )?,
                                    )),
                                vs => ::std::result::Result::Err(ctx_map(
                                    crate::dispatch::typed::Error::from_str(::std::format!(
                                        "expected an array with {} elements, found {}",
                                        3,
                                        <[_]>::len(vs),
                                    ))
                                )),
                            }
                        },
                        "FourTup" => {
                            let inner = crate::dispatch::Value::inner(&value);

                            let array = match crate::dispatch::TypedDeconstruct::type_kind(inner) {
                                crate::dispatch::TypeKind::Array =>
                                    crate::dispatch::TypedDeconstruct::as_array(inner),
                                t => return ::std::result::Result::Err(ctx_map(
                                    crate::dispatch::typed::Error::from_str(::std::format!(
                                        "expected an array type, found `{:?}`",
                                        t,
                                    ))
                                )),
                            };

                            match ::std::vec::Vec::as_slice(&array) {
                                [_field_0, _field_1, _field_2, _field_3,] =>
                                    ::std::result::Result::Ok(Self::FourTup(
                                        ::std::result::Result::map_err(
                                            crate::dispatch::Value::convert(_field_0),
                                            |e| ctx_map(crate::dispatch::typed::Error::context(
                                                e,
                                                ::std::format!(".{}", 0),
                                            )),
                                        )?,
                                        ::std::result::Result::map_err(
                                            crate::dispatch::Value::convert(_field_1),
                                            |e| ctx_map(crate::dispatch::typed::Error::context(
                                                e,
                                                ::std::format!(".{}", 1),
                                            )),
                                        )?,
                                        ::std::result::Result::map_err(
                                            crate::dispatch::Value::convert(_field_2),
                                            |e| ctx_map(crate::dispatch::typed::Error::context(
                                                e,
                                                ::std::format!(".{}", 2),
                                            )),
                                        )?,
                                        ::std::result::Result::map_err(
                                            crate::dispatch::Value::convert(_field_3),
                                            |e| ctx_map(crate::dispatch::typed::Error::context(
                                                e,
                                                ::std::format!(".{}", 3),
                                            )),
                                        )?,
                                    )),
                                vs => ::std::result::Result::Err(ctx_map(
                                    crate::dispatch::typed::Error::from_str(::std::format!(
                                        "expected an array with {} elements, found {}",
                                        4,
                                        <[_]>::len(vs),
                                    ))
                                )),
                            }
                        },
                        "SmallStruct" => {
                            let inner = crate::dispatch::Value::inner(&value);

                            let fields = match crate::dispatch::TypedDeconstruct::type_kind(inner) {
                                crate::dispatch::TypeKind::Struct =>
                                    crate::dispatch::TypedDeconstruct::as_struct(inner),
                                t => return ::std::result::Result::Err(ctx_map(
                                    crate::dispatch::typed::Error::from_str(::std::format!(
                                        "expected a struct type, found `{:?}`",
                                        t,
                                    ))
                                )),
                            };

                            let this = Self::SmallStruct {
                                x: {
                                    let s = "x";
                                    let val = ::std::option::Option::ok_or_else(
                                        ::std::collections::HashMap::remove(&mut fields, s),
                                        || ctx_map(crate::dispatch::typed::Error::from_str(
                                            ::std::format!("missing field `{}`", s)
                                        )),
                                    )?;
                                    ::std::result::Result::map_err(
                                        crate::dispatch::Value::convert(&val),
                                        |e| ctx_map(crate::dispatch::typed::Error::context(
                                            e,
                                            ::std::format!(".{}", s)
                                        )),
                                    )?
                                },
                                y: {
                                    let s = "y";
                                    let val = ::std::option::Option::ok_or_else(
                                        ::std::collections::HashMap::remove(&mut fields, s),
                                        || ctx_map(crate::dispatch::typed::Error::from_str(
                                            ::std::format!("missing field `{}`", s)
                                        )),
                                    )?;
                                    ::std::result::Result::map_err(
                                        crate::dispatch::Value::convert(&val),
                                        |e| ctx_map(crate::dispatch::typed::Error::context(
                                            e,
                                            ::std::format!(".{}", s)
                                        )),
                                    )?
                                },
                            };

                            if let ::std::option::Option::Some((f, _)) =
                                ::std::iter::Iterator::next(&mut ::std::collections::HashMap::iter(&fields))
                            {
                                return ::std::result::Result::Err(ctx_map(
                                    crate::dispatch::typed::Error::from_str(::std::format!(
                                        "unexpected field {:?}",
                                        f
                                    ))
                                ));
                            }

                            ::std::result::Result::Ok(this)
                        },
                        "BigStruct" => {
                            let inner = crate::dispatch::Value::inner(&value);

                            let fields = match crate::dispatch::TypedDeconstruct::type_kind(inner) {
                                crate::dispatch::TypeKind::Struct =>
                                    crate::dispatch::TypedDeconstruct::as_struct(inner),
                                t => return ::std::result::Result::Err(ctx_map(
                                    crate::dispatch::typed::Error::from_str(::std::format!(
                                        "expected a struct type, found `{:?}`",
                                        t,
                                    ))
                                )),
                            };

                            let this = Self::BigStruct {
                                desc: {
                                    let s = "desc";
                                    let val = ::std::option::Option::ok_or_else(
                                        ::std::collections::HashMap::remove(&mut fields, s),
                                        || ctx_map(crate::dispatch::typed::Error::from_str(
                                            ::std::format!("missing field `{}`", s)
                                        )),
                                    )?;
                                    ::std::result::Result::map_err(
                                        crate::dispatch::Value::convert(&val),
                                        |e| ctx_map(crate::dispatch::typed::Error::context(
                                            e,
                                            ::std::format!(".{}", s)
                                        )),
                                    )?
                                },
                                vals: {
                                    let s = "vals";
                                    let val = ::std::option::Option::ok_or_else(
                                        ::std::collections::HashMap::remove(&mut fields, s),
                                        || ctx_map(crate::dispatch::typed::Error::from_str(
                                            ::std::format!("missing field `{}`", s)
                                        )),
                                    )?;
                                    ::std::result::Result::map_err(
                                        crate::dispatch::Value::convert(&val),
                                        |e| ctx_map(crate::dispatch::typed::Error::context(
                                            e,
                                            ::std::format!(".{}", s)
                                        )),
                                    )?
                                },
                                id: {
                                    let s = "id";
                                    let val = ::std::option::Option::ok_or_else(
                                        ::std::collections::HashMap::remove(&mut fields, s),
                                        || ctx_map(crate::dispatch::typed::Error::from_str(
                                            ::std::format!("missing field `{}`", s)
                                        )),
                                    )?;
                                    ::std::result::Result::map_err(
                                        crate::dispatch::Value::convert(&val),
                                        |e| ctx_map(crate::dispatch::typed::Error::context(
                                            e,
                                            ::std::format!(".{}", s)
                                        )),
                                    )?
                                },
                                x: {
                                    let s = "x";
                                    let val = ::std::option::Option::ok_or_else(
                                        ::std::collections::HashMap::remove(&mut fields, s),
                                        || ctx_map(crate::dispatch::typed::Error::from_str(
                                            ::std::format!("missing field `{}`", s)
                                        )),
                                    )?;
                                    ::std::result::Result::map_err(
                                        crate::dispatch::Value::convert(&val),
                                        |e| ctx_map(crate::dispatch::typed::Error::context(
                                            e,
                                            ::std::format!(".{}", s)
                                        )),
                                    )?
                                },
                                y: {
                                    let s = "y";
                                    let val = ::std::option::Option::ok_or_else(
                                        ::std::collections::HashMap::remove(&mut fields, s),
                                        || ctx_map(crate::dispatch::typed::Error::from_str(
                                            ::std::format!("missing field `{}`", s)
                                        )),
                                    )?;
                                    ::std::result::Result::map_err(
                                        crate::dispatch::Value::convert(&val),
                                        |e| ctx_map(crate::dispatch::typed::Error::context(
                                            e,
                                            ::std::format!(".{}", s)
                                        )),
                                    )?
                                },
                            };

                            if let ::std::option::Option::Some((f, _)) =
                                ::std::iter::Iterator::next(&mut ::std::collections::HashMap::iter(&fields))
                            {
                                return ::std::result::Result::Err(ctx_map(
                                    crate::dispatch::typed::Error::from_str(::std::format!(
                                        "unexpected field {:?}",
                                        f
                                    ))
                                ));
                            }
                            ::std::result::Result::Ok(this)
                        },
                        unk => ::std::result::Result::Err(crate::dispatch::typed::Error::from_str(
                            ::std::format!("unknown enum variant {:?}", unk)
                        )),
                    }
                }
            }

            impl<T> crate::dispatch::TypedDeconstruct for Complex<T>
            where
                T: crate::dispatch::TypedDeconstruct,
                Self: 'static + ::std::marker::Send + ::std::marker::Sync + ::std::clone::Clone
            {
                fn type_kind(&self) -> crate::dispatch::TypeKind {
                    match self {
                        Self::FirstUnit => crate::dispatch::TypeKind::String,
                        Self::SecondUnit => crate::dispatch::TypeKind::String,
                        Self::FirstAmbiguous(a) => match crate::dispatch::TypedDeconstruct::type_kind(a) {
                            crate::dispatch::TypeKind::Unit => crate::dispatch::TypeKind::String,
                            _ => crate::dispatch::TypeKind::Struct,
                        },
                        Self::SecondAmbiguous(a) => match crate::dispatch::TypedDeconstruct::type_kind(a) {
                            crate::dispatch::TypeKind::Unit => crate::dispatch::TypeKind::String,
                            _ => crate::dispatch::TypeKind::Struct,
                        },
                        Self::SmallStruct { .. } => crate::dispatch::TypeKind::Struct,
                        Self::BigStruct { .. } => crate::dispatch::TypeKind::Struct,
                    }
                }

                fn clone_into_value(&self) -> crate::dispatch::Value<'static> {
                    crate::dispatch::Value::new(::std::clone::Clone::clone(self))
                }

                fn as_string(&self) -> ::std::string::String {
                    match self {
                        Self::FirstUnit =>
                            <::std::string::String as ::std::convert::From<_>>::from("FirstUnit"),
                        Self::SecondUnit =>
                            <::std::string::String as ::std::convert::From<_>>::from("SecondUnit"),
                        Self::FirstAmbiguous { .. } =>
                            <::std::string::String as ::std::convert::From<_>>::from("FirstAmbiguous"),
                        Self::SecondAmbiguous { .. } =>
                            <::std::string::String as ::std::convert::From<_>>::from("SecondAmbiguous"),
                        Self::ThreeTup { .. } =>
                            <::std::string::String as ::std::convert::From<_>>::from("ThreeTup"),
                        Self::FourTup { .. } =>
                            <::std::string::String as ::std::convert::From<_>>::from("FourTup"),
                        Self::SmallStruct { .. } =>
                            <::std::string::String as ::std::convert::From<_>>::from("SmallStruct"),
                        Self::BigStruct { .. } =>
                            <::std::string::String as ::std::convert::From<_>>::from("BigStruct"),
                    }
                }

                fn as_struct(
                    &self
                ) -> ::std::collections::HashMap<::std::string::String, crate::dispatch::Value> {
                    match self {
                        Self::FirstUnit => ::maplit::hashmap! {
                            <::std::string::String as ::std::convert::From<_>>::from("FirstUnit") =>
                                crate::dispatch::Value::new(()),
                        },
                        Self::SecondUnit => ::maplit::hashmap! {
                            <::std::string::String as ::std::convert::From<_>>::from("SecondUnit") =>
                                crate::dispatch::Value::new(()),
                        },
                        Self::FirstAmbiguous(v) => ::maplit::hashmap! {
                            <::std::string::String as ::std::convert::From<_>>::from("FirstAmbiguous") =>
                                crate::dispatch::Value::from_ref(v),
                        },
                        Self::SecondAmbiguous(v) => ::maplit::hashmap! {
                            <::std::string::String as ::std::convert::From<_>>::from("SecondAmbiguous") =>
                                crate::dispatch::Value::from_ref(v),
                        },
                        this @ Self::ThreeTup { .. } => {
                            #[repr(transparent)]
                            struct _V<T>(Complex<T>);
                            impl<T> crate::dispatch::TypedDeconstruct for _V<T>
                            where
                                T: crate::dispatch::TypedDeconstruct,
                                Self: 'static,
                                Complex<T>: Clone
                            {
                                fn type_kind(&self) -> crate::dispatch::TypeKind {
                                    crate::dispatch::TypeKind::Array
                                }

                                fn clone_into_value(&self) -> crate::dispatch::Value<'static> {
                                    crate::dispatch::Value::new(Self(::std::clone::Clone::clone(&self.0)))
                                }

                                fn as_array(&self) -> ::std::vec::Vec<crate::dispatch::Value> {
                                    match &self.0 {
                                        Complex::ThreeTup(_field_0, _field_1, _field_2,) => {
                                            ::std::vec![
                                                crate::dispatch::Value::from_ref(_field_0),
                                                crate::dispatch::Value::from_ref(_field_1),
                                                crate::dispatch::Value::from_ref(_field_2),
                                            ]
                                        }
                                        _ => ::std::unreachable!(),
                                    }
                                }
                            }

                            let val: &_V<T> = unsafe { ::std::mem::transmute(this) };
                            ::maplit::hashmap! {
                                <::std::string::String as ::std::convert::From<_>>::from("ThreeTup") =>
                                    crate::dispatch::Value::from_ref(val),
                            }
                        },
                        this @ Self::FourTup { .. } => {
                            #[repr(transparent)]
                            struct _V<T>(Complex<T>);
                            impl<T> crate::dispatch::TypedDeconstruct for _V<T>
                            where
                                T: crate::dispatch::TypedDeconstruct,
                                Self: 'static,
                                Complex<T>: Clone
                            {
                                fn type_kind(&self) -> crate::dispatch::TypeKind {
                                    crate::dispatch::TypeKind::Array
                                }

                                fn clone_into_value(&self) -> crate::dispatch::Value<'static> {
                                    crate::dispatch::Value::new(Self(::std::clone::Clone::clone(&self.0)))
                                }

                                fn as_array(&self) -> ::std::vec::Vec<crate::dispatch::Value> {
                                    match &self.0 {
                                        Complex::FourTup(_field_0, _field_1, _field_2, _field_3,) => {
                                            ::std::vec![
                                                crate::dispatch::Value::from_ref(_field_0),
                                                crate::dispatch::Value::from_ref(_field_1),
                                                crate::dispatch::Value::from_ref(_field_2),
                                                crate::dispatch::Value::from_ref(_field_3),
                                            ]
                                        }
                                        _ => ::std::unreachable!(),
                                    }
                                }
                            }

                            let val: &_V<T> = unsafe { ::std::mem::transmute(this) };
                            ::maplit::hashmap! {
                                <::std::string::String as ::std::convert::From<_>>::from("FourTup") =>
                                    crate::dispatch::Value::from_ref(val),
                            }
                        },
                        this @ Self::SmallStruct { .. } => {
                            #[repr(transparent)]
                            struct _V<T>(Complex<T>);
                            impl<T> crate::dispatch::TypedDeconstruct for _V<T>
                            where
                                T: crate::dispatch::TypedDeconstruct,
                                Self: 'static,
                                Complex<T>: Clone
                            {
                                fn type_kind(&self) -> crate::dispatch::TypeKind {
                                    crate::dispatch::TypeKind::Struct
                                }

                                fn clone_into_value(&self) -> crate::dispatch::Value<'static> {
                                    crate::dispatch::Value::new(Self(::std::clone::Clone::clone(&self.0)))
                                }

                                fn as_struct(
                                    &self
                                ) -> ::std::collections::HashMap<::std::string::String, crate::dispatch::Value>
                                {
                                    match &self.0 {
                                        Complex::SmallStruct { x, y, } => {
                                            ::maplit::hashmap! {
                                                <::std::string::String as ::std::convert::From<_>>::from("x") =>
                                                    crate::dispatch::Value::from_ref(x),
                                                <::std::string::String as ::std::convert::From<_>>::from("y") =>
                                                    crate::dispatch::Value::from_ref(y),
                                            }
                                        }
                                        _ => ::std::unreachable!(),
                                    }
                                }
                            }

                            let val: &_V<T> = unsafe { ::std::mem::transmute(this) };
                            ::maplit::hashmap! {
                                <::std::string::String as ::std::convert::From<_>>::from("SmallStruct") =>
                                    crate::dispatch::Value::from_ref(val),
                            }
                        },
                        this @ Self::BigStruct { .. } => {
                            #[repr(transparent)]
                            struct _V<T>(Complex<T>);
                            impl<T> crate::dispatch::TypedDeconstruct for _V<T>
                            where
                                T: crate::dispatch::TypedDeconstruct,
                                Self: 'static,
                                Complex<T>: Clone
                            {
                                fn type_kind(&self) -> crate::dispatch::TypeKind {
                                    crate::dispatch::TypeKind::Struct
                                }

                                fn clone_into_value(&self) -> crate::dispatch::Value<'static> {
                                    crate::dispatch::Value::new(Self(::std::clone::Clone::clone(&self.0)))
                                }

                                fn as_struct(
                                    &self
                                ) -> ::std::collections::HashMap<::std::string::String, crate::dispatch::Value> {
                                    match &self.0 {
                                        Complex::BigStruct { desc, vals, id, x, y, } => {
                                            ::maplit::hashmap! {
                                                <::std::string::String as ::std::convert::From<_>>::from("desc") =>
                                                    crate::dispatch::Value::from_ref(desc),
                                                <::std::string::String as ::std::convert::From<_>>::from("vals") =>
                                                    crate::dispatch::Value::from_ref(vals),
                                                <::std::string::String as ::std::convert::From<_>>::from("id") =>
                                                    crate::dispatch::Value::from_ref(id),
                                                <::std::string::String as ::std::convert::From<_>>::from("x") =>
                                                    crate::dispatch::Value::from_ref(x),
                                                <::std::string::String as ::std::convert::From<_>>::from("y") =>
                                                    crate::dispatch::Value::from_ref(y),
                                            }
                                        }
                                        _ => ::std::unreachable!(),
                                    }
                                }
                            }
                            let val: &_V<T> = unsafe { ::std::mem::transmute(this) };
                            ::maplit::hashmap! {
                                <::std::string::String as ::std::convert::From<_>>::from("BigStruct") =>
                                    crate::dispatch::Value::from_ref(val),
                            }
                        },
                    }
                }
            }
        }
    }
}
