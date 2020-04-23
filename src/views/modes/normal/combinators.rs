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
