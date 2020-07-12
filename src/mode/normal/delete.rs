//! Deletion-related `KeyEvent` parsing for "normal" mode

use super::combinators::{chain, numerical, set, single, wrap, Set, SetResult};
use super::movement::Parser as MoveParser;
use super::ParseResult::{self, Failed, NeedsMore, Success};
use super::{ParseState, Priority};
use crate::event::KeyEvent;
use crate::mode::HorizMove::LineBoundary;
use crate::mode::{Cmd, DeleteKind, Movement};
use std::marker::PhantomData;

/// A parser for handling all types of deletion functionality
pub struct Parser<T> {
    parsers: Set<Option<DeleteKind>>,
    _marker: PhantomData<T>,
}

impl<T> Parser<T> {
    pub fn new() -> Self {
        let eol = |(amount, _): (Option<usize>, KeyEvent)| {
            Some(DeleteKind::ByMovement {
                movement: Movement::RightCross(LineBoundary),
                amount: amount.unwrap_or(1),
                from_inclusive: true,
                to_inclusive: false,
            })
        };

        fn wrap_by_movement(
            tup: ((Option<usize>, KeyEvent), (Option<usize>, Movement)),
        ) -> Option<DeleteKind> {
            use crate::mode::{
                CharPredicate::ToChar,
                DeleteKind::{ByLines, ByMovement},
                HorizMove::{UntilFst, UntilSnd},
                Movement::{Down, Left, LeftCross, Right, RightCross, ToBottom, ToLine, ToTop, Up},
            };

            let ((n, _), (m, movement)) = tup;
            let amount = n.unwrap_or(1).checked_mul(m.unwrap_or(1))?;

            Some(match movement {
                Up | Down => ByLines { movement, amount },
                Left(_) | LeftCross(_) => ByMovement {
                    movement,
                    amount,
                    from_inclusive: false,
                    to_inclusive: true,
                },
                // This is a strange edge case that we need to deal with in order to make {n}G
                // behave separately from repetitions of G.
                ToBottom if m.is_some() => ByLines {
                    movement: ToLine(amount),
                    amount: 1,
                },
                ToLine(_) | ToTop | ToBottom => ByLines {
                    movement,
                    amount: 1,
                },
                Right(UntilFst(_))
                | RightCross(UntilFst(_))
                | Right(UntilSnd(ToChar(_)))
                | RightCross(UntilSnd(ToChar(_))) => ByMovement {
                    movement,
                    amount,
                    from_inclusive: true,
                    to_inclusive: true,
                },
                Right(_) | RightCross(_) => ByMovement {
                    movement,
                    amount,
                    from_inclusive: true,
                    to_inclusive: false,
                },
            })
        }

        fn wrap_lines(
            tup: ((Option<usize>, KeyEvent), (Option<usize>, KeyEvent)),
        ) -> Option<DeleteKind> {
            let ((n, _), (m, _)) = tup;
            let amount = n.unwrap_or(1).checked_mul(m.unwrap_or(1))?;

            Some(DeleteKind::CurrentLine { amount })
        }

        Self {
            _marker: PhantomData,
            parsers: set(vec![
                Box::new(wrap(
                    numerical(single(KeyEvent::shift('D'), Priority::Builtin)),
                    eol,
                )),
                Box::new(wrap(
                    chain(
                        numerical(single(KeyEvent::none('d'), Priority::Builtin)),
                        numerical(MoveParser::new()),
                        Priority::Builtin,
                    ),
                    wrap_by_movement,
                )),
                Box::new(wrap(
                    chain(
                        numerical(single(KeyEvent::none('d'), Priority::Builtin)),
                        numerical(single(KeyEvent::none('d'), Priority::Builtin)),
                        Priority::Builtin,
                    ),
                    wrap_lines,
                )),
            ]),
        }
    }
}

impl<T> ParseState for Parser<T> {
    type Output = Vec<Cmd<T>>;

    fn add(&mut self, key: KeyEvent) -> ParseResult<Self::Output> {
        match self.parsers.add(key) {
            Failed => Failed,
            NeedsMore => NeedsMore,
            Success(priority, SetResult::Success(Some(delete_kind))) => {
                Success(priority, vec![Cmd::Delete(delete_kind)])
            }
            // FIXME
            Success(_, _) => todo!(),
        }
    }

    fn max_priority(&self) -> Option<Priority> {
        self.parsers.max_priority()
    }
}
