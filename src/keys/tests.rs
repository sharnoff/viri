//! Various tests for the key parsing system
//!
//! Most of these tests *do not* exist to ensure that basic utilities function as expected. For
//! example: the `Map` combinator is *probably* ok and doesn't need testing. These are instead here
//! to ensure that the finer behaviors of combinators like: `Any`, `All`, and `Repeat` function as
//! intended.
//!
//! Because of this, the tests are essentially only based around character keys with no modifiers,
//! and only for the *type* of output -- not the actual value returned on a successful parse
//! (typically these are also just correct by construction).

use super::ParseResult::*;
use super::*;
use crate::event::KeyCode;
use std::cell::Cell;
use std::mem::ManuallyDrop;
use std::rc::Rc;

// Helper function to convert a string to `Vec<KeyEvent>` where each key has no modifiers
fn to_keys(chars: &str) -> Vec<KeyEvent> {
    chars
        .chars()
        .map(|c| KeyEvent {
            code: KeyCode::Char(c),
            mods: None,
        })
        .collect()
}

// Helper type that always returns exactly the given `ParseResult`s when called sequentially
//
// This lets us precisely mock arbitrary parsing logic
struct Exactly<T> {
    // The expected sequence of events, along with the result to return
    results: Vec<(&'static str, ParseResult<T>)>,
    remaining: Rc<Cell<usize>>,
}

struct Remaining {
    inner: Rc<Cell<usize>>,
}

impl<T: Copy> Exactly<T> {
    fn new(rem: &Remaining, results: &[(&'static str, ParseResult<T>)]) -> Self {
        rem.inner.set(results.len());

        Exactly {
            results: results.to_vec(),
            remaining: rem.inner.clone(),
        }
    }
}

impl Remaining {
    fn new() -> Self {
        Remaining {
            inner: Rc::new(Cell::new(usize::MAX)),
        }
    }

    fn check(self) {
        let cancel_drop = ManuallyDrop::new(self);
        let this = &*cancel_drop;
        if this.inner.get() != 0 {
            panic!("parser called fewer times than expected");
        }
    }
}

impl Drop for Remaining {
    fn drop(&mut self) {
        // We don't want to double panic, because that'll make the runtime unhappy and we won't
        // get *any* panic output. But if everything else says it's fine, we do want to panic here.
        if !std::thread::panicking() {
            panic!("`Remaining` not checked")
        }
    }
}

impl<T: Copy> KeyParser for Exactly<T> {
    type Output = T;

    fn parse(&self, keys: &mut KeyStream) -> ParseResult<T> {
        let remaining = self.remaining.get();

        if remaining == 0 {
            panic!("parser called more times than expected");
        }

        let pos = self.results.len() - remaining;
        let (key_str, res) = self.results[pos];
        let expected_keys = to_keys(key_str);

        for e in expected_keys {
            assert_eq!(Some(e), keys.next());
        }

        // `self.remaining -= 1`
        self.remaining.set(remaining - 1);
        res
    }
}

// Helper function for constructing `Success` variants
fn success<T>(val: T, could_take_more: bool) -> ParseResult<T> {
    Success {
        val,
        could_take_more,
    }
}

// Checks that `Repeat` successfully handles various kinds of edge cases
#[test]
#[rustfmt::skip]
fn repeat_edge_cases() {
    let cases: &[(&str, usize, ParseResult<usize>, &[(&str, ParseResult<()>)])] = &[
        ("", 0, success(0, true), &[]),
        ("abc", 0, success(0, false), &[("a", Fail)]),
        ("abc", 1, success(1, false), &[
            ("a", Success { val: (), could_take_more: false }),
            ("b", Fail),
        ]),
        ("abc", 3, NeedsMore, &[
            ("a", Success { val: (), could_take_more: false }),
            ("bc", NeedsMore),
        ]),
    ];

    for (i, &(src, stream_pos, output, exactly_args)) in cases.iter().enumerate() {
        println!("case {}...", i);

        let rem = Remaining::new();
        let parser = Repeat(Exactly::new(&rem, exactly_args));

        let expected_output = output.map(|n| vec![(); n]);

        let keys = to_keys(src);
        let mut stream = KeyStream::new(&keys);
        let res = parser.parse(&mut stream);

        assert_eq!(res, expected_output);
        assert_eq!(stream.pos, stream_pos);
        rem.check();
    }
}

#[test]
#[rustfmt::skip]
fn any_edge_cases() {
    // The cases presented here don't need to be in any particular order -- they're dealt with in
    // each permutation later on.
    let cases: &[(_, _, ParseResult<i32>, _)] = &[
        // If everything fails, we fail with the shortest length failure
        ("abc", 1, Fail, (
            // "consumes 'a' successfully, fails after seeing an unexpected 'b'"
            &[("ab", Fail)],
            // ... etc
            &[("a", Fail)],
            &[("abc", Fail)],
        )),
        // `NeedsMore` with no success or conflicts returns `NeedsMore`
        ("abc", 3, NeedsMore, (
            &[("ab", Fail)],
            &[("abc", Fail)],
            &[("abc", NeedsMore)],
        )),
        // Successes are prioritized by length
        ("abc", 3, success(3_i32, true), (
            &[("a", success(1_i32, false))],
            &[("ab", success(2, false))],
            &[("abc", success(3, true))],
        )),
        // Success when a `NeedsMore` is present has `could_take_more = true`
        ("abc", 3, success(1_i32, true), (
            &[("abc", success(1, false))],
            &[("abc", NeedsMore)],
            &[("a", Fail)],
        )),
        // Longer success takes priority over shorter conflicts
        ("abc", 3, success(3_i32, false), (
            &[("ab", success(1, false))],
            &[("ab", success(2, false))],
            &[("abc", success(3, false))],
        )),
        // Multiple longest successes produce a conflict
        ("abc", 3, Conflict { could_take_more: false }, (
            &[("ab", success(1, false))],
            &[("abc", success(2, false))],
            &[("abc", success(3, false))],
        )),
        // ... but those conflicts could take more if one of them can
        ("abc", 3, Conflict { could_take_more: true }, (
            &[("ab", success(1, false))],
            &[("abc", success(2, true))],
            &[("abc", success(3, false))],
        )),
        // Longer conflicts take priority over shorter successes
        ("abc", 3, Conflict { could_take_more: false }, (
            &[("a", success(1, false))],
            &[("ab", success(2, false))],
            &[("abc", Conflict { could_take_more: false })],
        )),
    ];

    for (i, &(src, stream_pos, output, (arg0, arg1, arg2))) in cases.iter().enumerate() {
        // Execute for each permutation of `arg{0,1,2}`
        let perms = &[
            (arg0, arg1, arg2),
            (arg0, arg2, arg1),
            (arg1, arg0, arg2),
            (arg1, arg2, arg0),
            (arg2, arg0, arg1),
            (arg2, arg1, arg0),
        ];

        for (j, &(a0, a1, a2)) in perms.iter().enumerate() {
            println!("case {}.{}...", i, j);

            let rem0 = Remaining::new();
            let rem1 = Remaining::new();
            let rem2 = Remaining::new();

            let parser = Any((
                Exactly::new(&rem0, a0),
                Exactly::new(&rem1, a1),
                Exactly::new(&rem2, a2),
            ));

            let keys = to_keys(src);
            let mut stream = KeyStream::new(&keys);
            let res = parser.parse(&mut stream);

            assert_eq!(res, output);
            assert_eq!(stream.pos, stream_pos);

            rem0.check();
            rem1.check();
            rem2.check();
        }
    }
}

#[test]
#[rustfmt::skip]
fn all_edge_cases() {
    type Arg<'a> = &'a [(&'static str, ParseResult<()>)];

    type Cases<'a> = &'a [
        (&'static str, usize, ParseResult<((), (), ())>, (Arg<'a>, Arg<'a>, Arg<'a>))
    ];

    let cases: Cases = &[
        // Failures at any point *do* produce a failure
        ("abc", 1, Fail, (
            &[("a", Fail)],
            &[],
            &[],
        )),
        ("abc", 2, Fail, (
            &[("a", success((), false))],
            &[("b", Fail)],
            &[],
        )),
        ("abc", 3, Fail, (
            &[("a", success((), false))],
            &[("b", success((), false))],
            &[("c", Fail)],
        )),

        // Conflicts are handled correctly:
        ("abc", 3, Conflict { could_take_more: false }, (
            &[("ab", success((), false))],
            &[("c", Conflict { could_take_more: false })],
            &[],
        )),

        // Normal success works:
        ("abcdef", 5, success(((), (), ()), true), (
            &[("ab", success((), false))],
            &[("cd", success((), false))],
            &[("e", success((), true))],
        )),
    ];

    for (i, &(src, stream_pos, output, (arg0, arg1, arg2))) in cases.iter().enumerate() {
        println!("case {}...", i);

        let rem0 = Remaining::new();
        let rem1 = Remaining::new();
        let rem2 = Remaining::new();

        let parser = All((
            Exactly::new(&rem0, arg0),
            Exactly::new(&rem1, arg1),
            Exactly::new(&rem2, arg2),
        ));

        let keys = to_keys(src);
        let mut stream = KeyStream::new(&keys);
        let res = parser.parse(&mut stream);

        assert_eq!(res, output);
        assert_eq!(stream.pos, stream_pos);

        rem0.check();
        rem1.check();
        rem2.check();
    }
}
