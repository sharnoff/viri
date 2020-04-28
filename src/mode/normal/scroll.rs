//! Scrolling-related `KeyEvent` parsing for "normal" mode

use super::combinators::{chain, numerical, set, single, wrap, Set, SetResult};
use super::ParseResult::{self, Failed, NeedsMore, Success};
use super::{ParseState, Priority};
use crate::event::KeyEvent;
use crate::mode::{Cmd, Direction, ScrollKind};

/// The parser responsible for the full handling of scrolling
pub struct Parser<T> {
    parsers: Set<Vec<Cmd<T>>>,
}

impl<T: 'static> Parser<T> {
    pub fn new() -> Self {
        use Cmd::Scroll;
        use Direction::{Down, Left, Right, Up};
        use ScrollKind::{ByDirection, DownPage, UpPage, VerticalCenter};

        let up = wrap(
            numerical(single(KeyEvent::ctrl('y'), Priority::Builtin)),
            |(n, _)| vec![Scroll(ByDirection(Up), n.unwrap_or(1))],
        );

        let down = wrap(
            numerical(single(KeyEvent::ctrl('e'), Priority::Builtin)),
            |(n, _)| vec![Scroll(ByDirection(Down), n.unwrap_or(1))],
        );

        let left = wrap(
            chain(
                numerical(single(KeyEvent::none('z'), Priority::Builtin)),
                numerical(single(KeyEvent::none('h'), Priority::Builtin)),
                Priority::Builtin,
            ),
            |((n, _), (m, _))| {
                vec![Scroll(
                    ByDirection(Left),
                    n.unwrap_or(1).saturating_mul(m.unwrap_or(1)),
                )]
            },
        );

        let right = wrap(
            chain(
                numerical(single(KeyEvent::none('z'), Priority::Builtin)),
                numerical(single(KeyEvent::none('l'), Priority::Builtin)),
                Priority::Builtin,
            ),
            |((n, _), (m, _))| {
                vec![Scroll(
                    ByDirection(Right),
                    n.unwrap_or(1).saturating_mul(m.unwrap_or(1)),
                )]
            },
        );

        let center = wrap(
            chain(
                single(KeyEvent::none('z'), Priority::Builtin),
                single(KeyEvent::none('z'), Priority::Builtin),
                Priority::Builtin,
            ),
            |_| vec![Scroll(VerticalCenter, 1)],
        );

        let half_page_up = wrap(
            numerical(single(KeyEvent::ctrl('u'), Priority::Builtin)),
            |(n, _)| {
                log::trace!("half page up!");
                vec![Scroll(UpPage(0.5), n.unwrap_or(1))]
            },
        );

        let half_page_down = wrap(
            numerical(single(KeyEvent::ctrl('d'), Priority::Builtin)),
            |(n, _)| {
                log::trace!("half page down!");
                vec![Scroll(DownPage(0.5), n.unwrap_or(1))]
            },
        );

        Self {
            parsers: set(vec![
                Box::new(up),
                Box::new(down),
                Box::new(left),
                Box::new(right),
                Box::new(center),
                Box::new(half_page_up),
                Box::new(half_page_down),
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
            Success(priority, SetResult::Success(cmds)) => Success(priority, cmds),
            // FIXME
            Success(_, _) => todo!(),
        }
    }

    fn max_priority(&self) -> Option<Priority> {
        self.parsers.max_priority()
    }
}
