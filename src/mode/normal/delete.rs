//! Deletion-related `KeyEvent` parsing for "normal" mode

use std::marker::PhantomData;

use crate::event::KeyEvent;
use crate::mode::HorizMove::LineBoundary;
use crate::mode::{Cmd, DeleteKind, Movement};
#[allow(unused_imports)]
use crate::prelude::*;

use super::combinators::{chain, numerical, set, single, wrap, Set, SetResult};
use super::movement::Parser as MoveParser;
use super::ParseResult::{self, Failed, NeedsMore, Success};
use super::{ParseState, Priority};

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
                DeleteKind::{ByLines, ByMovement},
                HorizMove::UntilSnd,
                Movement::{Down, Left, LeftCross, Right, RightCross, Up},
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
                Right(UntilSnd(_)) | RightCross(UntilSnd(_)) => ByMovement {
                    movement,
                    amount,
                    from_inclusive: true,
                    to_inclusive: false,
                },
                Right(_) | RightCross(_) => ByMovement {
                    movement,
                    amount,
                    from_inclusive: true,
                    to_inclusive: true,
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
                    numerical(single(KeyEvent::none('D'), Priority::Builtin)),
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
    type Output = Seq<Cmd<T>>;

    fn add(&mut self, key: KeyEvent) -> ParseResult<Self::Output> {
        match self.parsers.add(key) {
            Failed => Failed,
            NeedsMore => NeedsMore,
            Success(priority, SetResult::Success(Some(delete_kind))) => {
                Success(priority, One(Cmd::Delete(delete_kind)))
            }
            // FIXME
            Success(_, _) => todo!(),
        }
    }

    fn max_priority(&self) -> Option<Priority> {
        self.parsers.max_priority()
    }
}
