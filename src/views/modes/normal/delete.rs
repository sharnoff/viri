//! Deletion-related `KeyEvent` parsin for "normal" mode

use crate::event::KeyEvent;
use crate::views::Movement;

use super::combinators::{numerical, Numerical};
use super::movement;
use super::ParseResult::{Failed, NeedsMore, Success};
use super::{ParseResult, ParseState, Priority};

/// A base parser for different types of deletion functionality
///
/// It currently only supports deletion by movements, though this will be changed
pub(super) struct Parser {
    matched_prefix: bool,
    movement: Numerical<movement::Parser>,
}

impl Default for Parser {
    fn default() -> Self {
        Self {
            matched_prefix: false,
            movement: numerical(movement::Parser::default()),
        }
    }
}

impl ParseState for Parser {
    type Output = (usize, Movement);

    fn add(&mut self, key: KeyEvent) -> ParseResult<Self::Output> {
        if !self.matched_prefix {
            // TODO: This is hard-coded at the moment; it will be changed soon
            if key != KeyEvent::none('d') {
                return Failed;
            }

            self.matched_prefix = true;
            return ParseResult::NeedsMore;
        }

        match self.movement.add(key) {
            Failed => Failed,
            NeedsMore => NeedsMore,
            Success(priority, (n, m)) => Success(priority, (n.unwrap_or(1), m)),
        }
    }

    fn max_priority(&self) -> Option<Priority> {
        // Currently just completely deferring
        self.movement.max_priority()
    }
}
