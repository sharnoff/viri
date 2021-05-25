//! Base-level parsers for individual components

use super::{KeyParser, KeyStream, ModifierSet, ParseResult};
use crate::event::{KeyCode, KeyCode::Char, KeyEvent};
use std::ops::RangeBounds;

/// Parser for any character in a range with the given modifiers, returning the character chosen
pub struct Range<R>(pub R, pub ModifierSet);

/// Parser for any character with the given modifiers, returning the character
pub struct AnyChar(pub ModifierSet);

/// A parser for a particular key with any of the modifiers
///
/// Parses into a value of `()`.
pub struct Key(pub KeyCode, pub ModifierSet);

impl<R: RangeBounds<char>> KeyParser for Range<R> {
    type Output = char;

    fn parse(&self, keys: &mut KeyStream) -> ParseResult<Self::Output> {
        match keys.next() {
            Some(KeyEvent {
                code: Char(c),
                mods,
            }) => {
                if self.1.contains(mods.into()) && self.0.contains(&c) {
                    ParseResult::Success {
                        val: c,
                        could_take_more: false,
                    }
                } else {
                    ParseResult::Fail
                }
            }
            Some(_) => ParseResult::Fail,
            None => ParseResult::NeedsMore,
        }
    }
}

impl KeyParser for AnyChar {
    type Output = char;

    #[rustfmt::skip]
    fn parse(&self, keys: &mut KeyStream) -> ParseResult<Self::Output> {
        match keys.next() {
            Some(KeyEvent { code: Char(c), mods }) if self.0.contains(mods.into()) => {
                ParseResult::Success {
                    val: c,
                    could_take_more: false,
                }
            }
            Some(_) => ParseResult::Fail,
            None => ParseResult::NeedsMore,
        }
    }
}

impl KeyParser for Key {
    type Output = ();

    fn parse(&self, keys: &mut KeyStream) -> ParseResult<Self::Output> {
        match keys.next() {
            Some(KeyEvent { code, mods }) => {
                if code == self.0 && self.1.contains(mods.into()) {
                    ParseResult::Success {
                        val: (),
                        could_take_more: false,
                    }
                } else {
                    ParseResult::Fail
                }
            }
            None => ParseResult::NeedsMore,
        }
    }
}
