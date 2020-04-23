//! Parser combinators for managing input in "normal" mode

use crate::event::{KeyCode, KeyEvent, KeyModifiers as Mods};

use super::ParseResult::{Failed, NeedsMore, Success};
use super::{ParseResult, ParseState, Priority};

pub(super) fn numerical<P: ParseState>(parser: P) -> Numerical<P> {
    Numerical {
        number: None,
        started_parser: false,
        parser,
    }
}

pub(super) fn wrap<P: ParseState, T>(parser: P, func: fn(P::Output) -> T) -> Wrap<P, T> {
    Wrap { parser, func }
}

pub(super) fn set<T>(parsers: Vec<Box<dyn ParseState<Output = T>>>) -> Set<T> {
    Set { parsers }
}

/// A parser that (optionally) prefixes another parser by a numer
///
/// This is used in contexts like movements to allow the logic for the parser itself to be handled
/// separately from the number of repetitions.
#[derive(Default)]
pub(super) struct Numerical<P: ParseState> {
    number: Option<usize>,
    started_parser: bool,
    parser: P,
}

impl<P: ParseState> ParseState for Numerical<P> {
    type Output = (Option<usize>, P::Output);

    fn add(&mut self, key: KeyEvent) -> ParseResult<Self::Output> {
        // ch is Some(_) if we're going to add it to `self.number`
        let ch = if self.started_parser || key.mods != Mods::NONE {
            None
        } else {
            match key.code {
                KeyCode::Char(c) => match c {
                    '0' if self.number.is_some() => Some(c),
                    '1'..='9' => Some(c),
                    _ => None,
                },
                _ => None,
            }
        };

        if ch.is_none() {
            self.started_parser = true;
        }

        if let Some(c) = ch {
            let n = (c as u8) - b'0';
            let new = self
                .number
                .unwrap_or(0)
                .checked_mul(10)
                .and_then(|x| x.checked_add(n as usize));

            match new {
                // TODO: We need some way of managing the error here - someone overflowed the value
                // and that should probably behandled gracefully but also let them know
                None => ParseResult::Success(Priority::Error, todo!()),
                Some(number) => {
                    self.number = Some(number);
                    ParseResult::NeedsMore
                }
            }
        } else {
            // ch as None means that we just go directly to the parser
            match self.parser.add(key) {
                Success(priority, out) => Success(priority, (self.number, out)),
                NeedsMore => NeedsMore,
                Failed => Failed,
            }
        }
    }

    fn max_priority(&self) -> Option<Priority> {
        self.parser.max_priority()
    }
}

/// A parser that wraps the output of `P` by applying the function `F`
pub(super) struct Wrap<P: ParseState, T> {
    parser: P,
    func: fn(P::Output) -> T,
}

impl<P: ParseState, T> ParseState for Wrap<P, T> {
    type Output = T;

    fn add(&mut self, key: KeyEvent) -> ParseResult<T> {
        match self.parser.add(key) {
            Success(priority, v) => Success(priority, (self.func)(v)),
            NeedsMore => NeedsMore,
            Failed => Failed,
        }
    }

    fn max_priority(&self) -> Option<Priority> {
        self.parser.max_priority()
    }
}

/// A parser that matches over any parser in the set
///
/// The `ParseState` output type for a `Set` is a `SetResult<T>`, which
pub(super) struct Set<T> {
    parsers: Vec<Box<dyn ParseState<Output = T>>>,
}

/// The parsing output type of [`Set`]
///
/// [`Set`]: struct.Set.html
pub(super) enum SetResult<T> {
    /// A successful parse; there were no priority conflicts in producing this value
    Success(T),

    /// A partial conflict: a single value was produced, but other parsers with equal (or greater)
    /// priority may produce others.
    PartialConflict(T),

    /// A conflict resulting from multiple equal-priority parsers producing output at the same time
    ///
    /// This conflict should be turned into an error of some form, but it is left to the caller to
    /// determine how to do this.
    FinishConflict,
}

impl<T> ParseState for Set<T> {
    type Output = SetResult<T>;

    fn add(&mut self, key: KeyEvent) -> ParseResult<SetResult<T>> {
        // A helper type for managing the different failure modes that may occur within this
        // function
        enum SearchResult<S> {
            Single(Priority, S),
            Conflict(Priority),
            Nothing,
        }

        use SearchResult::*;

        impl<S> SearchResult<S> {
            fn priority(&self) -> Option<Priority> {
                match self {
                    Single(p, _) | Conflict(p) => Some(*p),
                    Nothing => None,
                }
            }
        }

        let mut found: SearchResult<T> = Nothing;
        let mut max_possible: Option<Priority> = None;
        let mut next_set: Vec<Box<dyn ParseState<Output = T>>> =
            Vec::with_capacity(self.parsers.len());

        let mut needs_more = false;

        for mut parser in self.parsers.drain(..) {
            match parser.add(key) {
                ParseResult::NeedsMore => {
                    needs_more = true;
                    max_possible = max_possible.max(parser.max_priority());
                    next_set.push(parser);
                }
                ParseResult::Failed => (),
                ParseResult::Success(priority, v) => match found {
                    Nothing => found = Single(priority, v),

                    Conflict(p) | Single(p, _) if p < priority => found = Single(priority, v),
                    Conflict(p) | Single(p, _) if p > priority => (),

                    // p == priority
                    Single(p, _) => found = Conflict(p),
                    Conflict(_) => (),
                },
            }
        }

        if max_possible.is_none() && found.priority().is_none() {
            return ParseResult::Failed;
        }

        match found {
            Single(priority, val) if Some(priority) > max_possible => {
                ParseResult::Success(priority, SetResult::Success(val))
            }
            Single(priority, val) => {
                // FIXME: What should the priority be here?
                self.parsers = next_set;
                ParseResult::Success(priority, SetResult::PartialConflict(val))
            }
            Conflict(_) => {
                return ParseResult::Success(Priority::Error, SetResult::FinishConflict);
            }
            Nothing => match needs_more {
                true => {
                    self.parsers = next_set;
                    ParseResult::NeedsMore
                }
                false => ParseResult::Failed,
            },
        }
    }

    fn max_priority(&self) -> Option<Priority> {
        self.parsers
            .iter()
            .map(|p| p.max_priority())
            .max()
            .unwrap_or(None)
    }
}
