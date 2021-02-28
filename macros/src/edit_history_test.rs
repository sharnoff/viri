#![allow(dead_code)]
//! Helper macro for testing an `EditHistory`
//!
//! More information about this macro is available in the documentation for that module's tests.

use derive_syn_parse::Parse;
use proc_macro::TokenStream;
use quote::{quote, quote_spanned};
use syn::parse::ParseStream;
use syn::punctuated::Punctuated;
use syn::{parse_macro_input, token, Ident, LitStr, Token};

// A helper trait for the `@<kwd>` syntax
trait Peek2 {
    fn peek2(input: ParseStream) -> bool;
}

mod kwd {
    use syn::custom_keyword;

    macro_rules! keywords {
        ($($name:ident),+$(,)?) => {
            $(
            custom_keyword!($name);

            impl super::Peek2 for $name {
                fn peek2(input: syn::parse::ParseStream) -> bool {
                    input.peek2($name)
                }
            }
            )*
        }
    }

    keywords! {
        start, edit, equals, undo, redo, print_graph
    }
}

#[derive(Parse)]
struct AtKwd<K: Peek2> {
    at_token: Token![@],
    kwd: K,
}

impl<K: Peek2> AtKwd<K> {
    fn peek(input: ParseStream) -> bool {
        input.peek(Token![@]) && K::peek2(input)
    }
}

#[derive(Parse)]
struct TestInput {
    _fn_token: Token![fn],
    test_name: Ident,
    #[paren]
    parens: token::Paren,
    #[brace]
    braces: token::Brace,

    #[inside(braces)]
    start: StartState,
    #[inside(braces)]
    semi: Token![;],

    #[inside(braces)]
    #[parse_terminated(TestCmd::parse)]
    body: Punctuated<TestCmd, Token![;]>,
}

#[derive(Parse)]
struct StartState {
    kwd: AtKwd<kwd::start>,
    start_str: LitStr,
}

#[rustfmt::skip]
macro_rules! at_kwd { ($name:ident) => { <AtKwd<kwd::$name>>::peek }; }

#[derive(Parse)]
enum TestCmd {
    #[peek_with(at_kwd![edit], name = "`@edit`")]
    Edit(AtKwd<kwd::edit>, EditCmd),

    #[peek_with(at_kwd![equals], name = "`@equals`")]
    Equals(AtKwd<kwd::equals>, LitStr),

    #[peek_with(at_kwd![undo], name = "`@undo`")]
    Undo(AtKwd<kwd::undo>, ChangeCmd),

    #[peek_with(at_kwd![redo], name = "`@redo`")]
    Redo(AtKwd<kwd::redo>, ChangeCmd),

    #[peek_with(at_kwd![print_graph], name = "`@print_graph`")]
    PrintGraph(AtKwd<kwd::print_graph>),
}

#[derive(Parse)]
struct EditCmd {
    #[peek(token::Bracket)]
    name: Option<EditName>,
    #[peek(token::Paren)]
    pre: Option<ParenCtx>,
    old_str: LitStr,
    #[peek(token::Paren)]
    post: Option<ParenCtx>,
    arrow: Token![=>],
    replacement: LitStr,
    #[peek(token::Paren)]
    removed_edits: Option<Edits>,
}

#[derive(Parse)]
struct ParenCtx {
    #[paren]
    paren: token::Paren,
    #[inside(paren)]
    ctx: LitStr,
}

#[derive(Parse)]
struct EditName {
    #[bracket]
    bracket: token::Bracket,
    #[inside(bracket)]
    ident: Ident,
}

#[derive(Parse)]
struct ChangeCmd {
    name: Ident,
    #[peek(token::Paren)]
    also: Option<Edits>,
}

#[derive(Parse)]
struct Edits {
    #[paren]
    paren: token::Paren,
    #[inside(paren)]
    #[parse_terminated(Ident::parse)]
    edits: Punctuated<Ident, Token![,]>,
}

#[rustfmt::skip]
pub fn edit_history_test(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as TestInput);

    // Generate the code for the function body. We start with `start`:
    let start_str = &input.start.start_str;
    let start_len = start_str.value().len();

    // Bring some things into scope, to make our life easier.
    let mut func_body = quote! {
        use ::std::collections::{BTreeMap, BTreeSet};
        use ::std::boxed::Box;
        use ::std::vec::Vec;
        use ::std::str::from_utf8 as str_from_utf8;
        use crate::text::diff::history::{EditHistory, EditId};
    };

    func_body.extend(quote_spanned! {
        input.start.start_str.span()=>
        let mut bytes = Vec::from(#start_str.as_bytes());
        let mut as_str = str_from_utf8(&bytes).unwrap();
    });
    func_body.extend(quote! {
        let mut ids = <BTreeMap<&str, EditId>>::new();
        let mut names = <BTreeMap<EditId, &str>>::new();
        let mut history = <EditHistory<usize, Box<[u8]>>>::new(#start_len);
        let mut next_time = 0_usize;
    });

    for cmd in input.body {
        let commmand_output = match cmd {
            TestCmd::PrintGraph(_) => {
                quote!(history.print_graph(|id| names.get(&id).cloned().unwrap_or("<unnamed>"));)
            }
            TestCmd::Edit(_, edit) => {
                let search_str = edit.pre.as_ref().map(|c| c.ctx.value()).unwrap_or_default()
                    + &edit.old_str.value()
                    + &edit.post.as_ref().map(|c| c.ctx.value()).unwrap_or_default();
                let ss = LitStr::new(&search_str, edit.old_str.span());
                let offset = edit.pre.map(|c| c.ctx.value().len()).unwrap_or(0);

                let old_str = &edit.old_str;
                let new_str = &edit.replacement;

                let removed = edit.removed_edits
                    .map(|es| es.edits.iter().map(ident_to_lit).collect())
                    .unwrap_or(Vec::new());

                let maybe_record_name = edit.name.map(|EditName { ident, .. }| {
                    let name = ident.to_string();
                    quote_spanned!(ident.span()=>
                        ids.insert(#name, res.new_id);
                        names.insert(res.new_id, #name);
                    )
                })
                .unwrap_or_default();

                quote_spanned! {edit.old_str.span()=>
                    // First, construct the original `Diff`:
                    let matches: ::std::vec::Vec<_> = as_str.matches(#ss).collect();
                    let diff_idx = match matches.as_slice() {
                        [] => panic!("bad test: no match for {:?} in {:?}", #ss, as_str),
                        [s] => {
                            s.as_ptr() as usize - as_str.as_ptr() as usize + #offset
                        }
                        [..] => {
                            panic!("bad test: more than one match for {:?} in {:?}", #ss, as_str)
                        }
                    };

                    // Diffs have `Box<[u8]>` as their backing type
                    let diff = crate::text::Diff {
                        diff_idx,
                        old: <Box<[u8]>>::from(#old_str.as_bytes()),
                        new: <Box<[u8]>>::from(#new_str.as_bytes()),
                    };

                    let res = history.edit(diff, next_time, [])
                        .expect("edit failed");
                    let expected_removed = (&[#( #removed, )*] as &[&str])
                        .iter()
                        .map(|name| {
                            ids.get(name)
                                .expect(&format!("bad test: no edit with name '{}'", name))
                                .clone()
                        })
                        .collect::<std::collections::BTreeSet<_>>();

                    let removed_set = res.removed.into_iter().collect::<std::collections::BTreeSet<_>>();
                    assert_eq!(expected_removed, removed_set);

                    #maybe_record_name

                    res.diffs.iter().for_each(|d| d.apply(&mut bytes));

                    as_str = ::std::str::from_utf8(&bytes)
                        .expect("edit did not result in utf8 string");
                    next_time += 1;
                }
            }
            TestCmd::Equals(_, string) => quote_spanned! {
                string.span()=>
                assert_eq!(as_str, #string);
            },
            TestCmd::Undo(_, change) => {
                let name = ident_to_lit(&change.name);
                let also = change.also
                    .map(|e| e.edits.iter().map(ident_to_lit).collect())
                    .unwrap_or(Vec::new());

                quote_spanned! {
                    name.span()=>
                    let id = ids.get(#name)
                        .cloned()
                        .expect(concat!("bad test: no edit with name '", #name, "'"));
                    let res = history.undo(id);

                    let expected_undos = [#name, #( #also, )*]
                        .iter()
                        .map(|n| {
                            ids.get(n).cloned()
                                .expect(&format!("bad test: no edit with name '{}'", n))
                        })
                        .collect::<std::collections::BTreeSet<_>>();
                    let actual_undos = res.undone
                        .into_iter()
                        .collect::<std::collections::BTreeSet<_>>();
                    assert_eq!(expected_undos, actual_undos);

                    res.diffs.iter().for_each(|d| d.apply(&mut bytes));
                    as_str = std::str::from_utf8(&bytes)
                        .expect("undo did not result in utf8 string");
                }
            }
            TestCmd::Redo(_, change) => {
                let name = ident_to_lit(&change.name);
                let also = change.also
                    .map(|e| e.edits.iter().map(ident_to_lit).collect())
                    .unwrap_or(Vec::new());

                quote_spanned! {
                    name.span()=>
                    let id = ids.get(#name)
                        .cloned()
                        .expect(concat!("bad test: no edit with name '", #name, "'"));
                    let res = history.redo(id);

                    let expected_redos = [#name, #( #also, )*]
                        .iter()
                        .map(|n| {
                            ids.get(n).cloned()
                                .expect(&format!("bad test: no edit with name '{}'", n))
                        })
                        .collect::<std::collections::BTreeSet<_>>();
                    let actual_redos = res.redone
                        .into_iter()
                        .collect::<std::collections::BTreeSet<_>>();
                    assert_eq!(expected_redos, actual_redos);

                    res.diffs.iter().for_each(|d| d.apply(&mut bytes));
                    as_str = std::str::from_utf8(&bytes)
                        .expect("redo did not result in utf8 string");
                }
            }
        };

        func_body.extend(commmand_output);
    }

    let name = input.test_name;
    quote!(
        #[test]
        #[allow(unused_assignments)]
        fn #name() {
            #func_body
        }
    )
    .into()
}

fn ident_to_lit(ident: &Ident) -> LitStr {
    LitStr::new(&ident.to_string(), ident.span())
}
