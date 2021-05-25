//! Parser combinators for keybindings

use super::{KeyParser, KeyStream, ParseResult};
use ParseResult::{Conflict, Fail, NeedsMore, Success};

/// Extension trait for `KeyParser`s to provide some additional functionality
pub trait KeyParserExt: Sized + KeyParser {
    /// Maps the parser by the given function, analagous to `Iterator::map`
    fn map<F, Out>(self, func: F) -> Map<Self, F>
    where
        F: Fn(Self::Output) -> Out,
    {
        Map { parser: self, func }
    }

    /// Returns a parser for either this one or the alternative
    fn or<P>(self, other: P) -> Any<(Self, P)>
    where
        P: KeyParser<Output = Self::Output>,
    {
        Any((self, other))
    }

    /// Returns a parser that parses this item and then the other parser's item
    fn then<P>(self, other: P) -> All<(Self, P)>
    where
        P: KeyParser,
    {
        All((self, other))
    }

    /// Returns a parser that repeats this one until failure
    fn repeat(self) -> Repeat<Self> {
        Repeat(self)
    }

    /// Returns a parser that parses exactly `n` occurences of this item
    fn count(self, n: usize) -> Count<Self> {
        Count(n, self)
    }
}

impl<P: Sized + KeyParser> KeyParserExt for P {}

/// Parser combinator that parses any parser in the tuple, but not more than one
pub struct Any<Tuple>(pub Tuple);

/// Parser combinator that parses everything in sequence
pub struct All<Tuple>(pub Tuple);

/// Parser combinator that maps a parser by a function
pub struct Map<P, F> {
    parser: P,
    func: F,
}

/// Parser that repeats indefinitely, until the provided parser no longer matches
///
/// Please note that -- if the inner parser returns `ParseResult::NeedsMore`, this will do the
/// same. It could have instead cut the repetitions short, but that doesn't happen to be what this
/// does.
///
/// Every successful parse using all of the input has `could_take_more = true`.
pub struct Repeat<P>(pub P);

/// Parser for a set number of occurences of the inner parser's output.
pub struct Count<P>(pub usize, pub P);

impl<P: KeyParser, F: Fn(P::Output) -> Out, Out> KeyParser for Map<P, F> {
    type Output = Out;

    fn parse(&self, keys: &mut KeyStream) -> ParseResult<Out> {
        self.parser.parse(keys).map(&self.func)
    }
}

impl<P: KeyParser> KeyParser for Repeat<P> {
    type Output = Vec<P::Output>;

    #[rustfmt::skip]
    fn parse(&self, keys: &mut KeyStream) -> ParseResult<Self::Output> {
        let mut outs = Vec::new();

        let could_take_more = loop {
            // We have to check if the stream is empty here, because we'd otherwise always return
            // `NeedsMore` for sequences satsifying a keybinding with trailing repetition
            if keys.peek().is_none() {
                break true;
            }

            let state = keys.state();
            match self.0.parse(keys) {
                Success { val, .. } => {
                    outs.push(val);
                }
                Conflict { could_take_more } => {
                    return Conflict { could_take_more };
                }
                Fail => {
                    // On failure, pretend we never tried to parse it
                    keys.restore(state);
                    break false;
                }
                NeedsMore => return NeedsMore,
            }
        };

        Success {
            val: outs,
            could_take_more,
        }
    }
}

impl<P: KeyParser> KeyParser for Count<P> {
    type Output = Vec<P::Output>;

    #[rustfmt::skip]
    fn parse(&self, keys: &mut KeyStream) -> ParseResult<Self::Output> {
        let mut outs = Vec::with_capacity(self.0);
        let mut could_take_more = false;

        while outs.len() < self.0 {
            match self.1.parse(keys) {
                Success { val, could_take_more: c } => {
                    outs.push(val);
                    could_take_more = c;
                }
                Conflict { could_take_more } => {
                    return Conflict { could_take_more };
                }
                Fail => return Fail,
                NeedsMore => return NeedsMore,
            }
        }

        Success {
            val: outs,
            could_take_more,
        }
    }
}

// Implementations of parsing for `Any` and `All`
macro_rules! impl_tuple {
    ($($names:ident $indexes:tt,)*) => {
        impl_tuple!(@do_impl $($names $indexes)*);
    };

    // Don't do anything for tuples of length 0 or 1
    (@do_impl $($name:ident $index:tt)?) => {};

    // Helper functionality to extract all but the last pair of name + index
    (@init $($name:ident $index:tt)* @mark $l_name:ident $l_index:tt) => {
        impl_tuple!(@do_impl $($name $index)*);
    };
    (@init $($hn:ident $hi:tt)* @mark $n:ident $i:tt $($tn:ident $ti:tt)+) => {
        impl_tuple!(@init $($hn $hi)* $n $i @mark $($tn $ti)*);
    };

    // Helper functionality to count a certain number of tokens
    (@count $head:tt $($tail:tt)*) => {{ 1 + impl_tuple!(@count $($tail)*) }};
    (@count) => {{ 0 }};

    // The actual implementations for tuples of various sizes:
    (@do_impl $head:ident $h_i:tt $($names:ident $index:tt)+) => {
        impl_tuple!(@init $head $h_i @mark $($names $index)+);

        impl<$head, $($names),+> KeyParser for Any<($head, $($names),+)>
        where
            $head: KeyParser,
            $($names: KeyParser<Output = $head::Output>,)+
        {
            type Output = $head::Output;

            fn parse(&self, keys: &mut KeyStream) -> ParseResult<$head::Output> {
                let mut results = Vec::with_capacity(impl_tuple!(@count $h_i $($index)*));
                let base_state = keys.state();
                {
                    let res = self.0.$h_i.parse(keys);
                    let state = keys.state();
                    results.push((state, res));
                    keys.restore(base_state);
                }
                $(
                {
                    let res = self.0.$index.parse(keys);
                    let state = keys.state();
                    results.push((state, res));
                    keys.restore(base_state);
                }
                )*

                // The index of the longest successful parse
                let mut longest_success = None;
                // The state corresponding to the longest successful parse OR the shortest failure,
                // if there were no successes.
                let mut longest_state = None;
                let mut longest_is_conflict = false;
                // Whether the longest parse could take more input
                let mut longest_could_take_more = false;
                // the state of the first result with `NeedsMore`. All other `NeedsMore` states
                // should be identical.
                let mut needsmore = None;

                for (i, &(state, ref res)) in results.iter().enumerate() {
                    //  ^        ^^^
                    // these two mean that we get an owned `state` but borrowed `res`
                    match res {
                        &Success { could_take_more, .. } => {
                            if Some(state) == longest_state {
                                longest_is_conflict = true;
                                longest_success = None;
                                longest_could_take_more |= could_take_more;
                            } else if Some(state) > longest_state {
                                longest_success = Some(i);
                                longest_state = Some(state);
                                longest_is_conflict = false;
                                longest_could_take_more = could_take_more;
                            }
                        }
                        &Conflict { could_take_more } => {
                            if Some(state) == longest_state {
                                longest_success = None;
                                longest_is_conflict = true;
                                longest_could_take_more |= could_take_more;
                            } else if Some(state) > longest_state {
                                // If there was a shorter success value, our longer conflict takes
                                // precedence
                                longest_success = None;
                                longest_state = Some(state);
                                longest_is_conflict = true;
                                longest_could_take_more = could_take_more;
                            }
                        }
                        &Fail => {
                            // Essentially: if there weren't any successful parses, ensure that
                            // `longest_length` is the shortest failure.
                            if longest_success.is_none() && !longest_is_conflict {
                                match longest_state {
                                    Some(s) if s < state => (),
                                    _ => longest_state = Some(state),
                                }
                            }
                        }
                        NeedsMore => match needsmore {
                            None => needsmore = Some(state),
                            Some(s) => assert!(s == state, "different `NeedsMore` states"),
                        },
                    }
                }

                longest_could_take_more |= needsmore.is_some();

                // We'll be returning whatever `longest_state` indicates. We need the state of the
                // key stream to agree with that.
                if let Some(s) = longest_state {
                    keys.restore(s);
                }

                match (longest_success, longest_state.is_some(), longest_is_conflict) {
                    (None, true, true) => Conflict {
                        could_take_more: longest_could_take_more,
                    },
                    (Some(i), true, _) => Success {
                        val: results.remove(i).1.unwrap(),
                        could_take_more: longest_could_take_more,
                    },
                    // Check for `NeedsMore` before failure, because it takes precedence
                    _ if needsmore.is_some() => {
                        // If so, we need to restore to the `NeedsMore` state:
                        keys.restore(needsmore.unwrap());
                        NeedsMore
                    }
                    (None, true, false) => Fail,
                    // TODO: is this really unreachable?
                    _ => unreachable!(),
                }
            }
        }

        impl<$head: KeyParser, $($names: KeyParser),+> KeyParser for All<($head, $($names),+)> {
            type Output = ( $head::Output, $($names::Output),+ );

            #[allow(non_snake_case)]
            fn parse(&self, keys: &mut KeyStream) -> ParseResult<Self::Output> {
                let mut could_take_more;

                // We repeatedly assign to `could_take_more`. Because we only care about the last
                // assignment, it's easier to just let the compiler optimize that out instead of
                // trying to extract out the last index in the macro.
                #[allow(unused_assignments)]
                let val = (
                    match self.0.$h_i.parse(keys) {
                        Success { val, could_take_more: c } => {
                            could_take_more = c;
                            val
                        },
                        Conflict { could_take_more } => return Conflict { could_take_more },
                        Fail => return Fail,
                        NeedsMore => return NeedsMore,
                    },
                    $(
                    match self.0.$index.parse(keys) {
                        Success { val, could_take_more: c } => {
                            could_take_more = c;
                            val
                        },
                        Conflict { could_take_more } => return Conflict { could_take_more },
                        Fail => return Fail,
                        NeedsMore => return NeedsMore,
                    },
                    )+
                );
                Success {
                    val,
                    could_take_more,
                }
            }
        }
    }
}

impl_tuple! {
    A 0, B 1, C 2, D 3, E 4, F 5, G 6, H 7, I 8, J 9, K 10, L 11, M 12,
}
