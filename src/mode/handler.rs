//! Items for abstraction over mode execution

use crate::event::KeyEvent;
use crate::prelude::*;

use super::{CursorStyle, DeleteKind, Direction, Error, Mode, ModeSet, Modes, Movement};

/// A generic handler for managing switching between multiple modes
pub struct Handler<E: Executor<Meta>, Meta: 'static> {
    /// The set of modes that we're allowed to transition to
    allowed_modes: ModeSet,

    /// The stack of modes - this is typically never has a size greater than two, but phrasing it
    /// this way allows greater generalization and code that is more understandable.
    mode_stack: Vec<Modes<Meta>>,

    /// The executor responsible for handling the commands produced by the current mode
    executor: E,
}

/// The commands provided to an [`Executor`] - a subset of [`mode::Cmd`]
///
/// [`Executor`]: trait.Executor.html
/// [`mode::Cmd`]: ../enum.Cmd.html
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Cmd<T> {
    /// A cursor movement, given by the direction and a number of repetitions
    Cursor(Movement, usize),

    /// A scrolling movement, given by the direction and number of lines or columns to scroll by
    Scroll(Direction, usize),

    /// An insertion of the given string at the current cursor position
    Insert(String),

    /// A deletion
    Delete(DeleteKind),

    /// Any other command that might be provided
    ///
    /// This is notably used in the case of [`views::Cmd`], which defines a type alias for
    /// `Cmd<views::MetaCmd<T>>`.
    ///
    /// [`views::Cmd`]: ../views/type.Cmd.html
    Other(T),
}

pub trait Executor<T> {
    type Output: Monad;

    fn execute(&mut self, cmd: Cmd<T>, cursor_style: CursorStyle) -> Self::Output;

    fn error(err: super::Error) -> Self::Output;
}

impl<Meta: 'static, E: Executor<Meta>> Handler<E, Meta> {
    /// Constructs a new `Handler` from an executor with the given initial mode and set of modes
    /// that may be transitioned to
    ///
    /// If the initial mode is not within the set of allowed modes, this function will panic. This
    /// is a simple `assert!`, so be mindful that you will not be handheld while shooting yourself
    /// in the foot.
    pub fn new(executor: E, init: impl Mode<Meta>, allowed_modes: ModeSet) -> Self {
        let modes: Modes<_> = init.xinto();

        assert!(allowed_modes.contains(modes.kind()));

        Self {
            allowed_modes,
            mode_stack: vec![modes],
            executor,
        }
    }

    /// Handles the given key event, producing output specified by the `Executor`
    pub fn handle(&mut self, key: KeyEvent) -> Vec<E::Output> {
        use super::Cmd::{ChangeMode, Cursor, Delete, EnterMode, ExitMode, Insert, Other, Scroll};

        let cmds = match self.mode_stack.last_mut().unwrap().try_handle(key) {
            Ok(c) => c,
            Err(e) => return vec![E::error(e)],
        };

        let mut outs = Vec::new();

        for cmd in cmds.into_iter() {
            let cmd = match cmd {
                Cursor(m, n) => Cmd::Cursor(m, n),
                Scroll(d, n) => Cmd::Scroll(d, n),
                Insert(s) => Cmd::Insert(s),
                Delete(kind) => Cmd::Delete(kind),
                Other(t) => Cmd::Other(t),
                ExitMode => {
                    if self.mode_stack.len() > 1 {
                        self.mode_stack.pop();
                        continue;
                    } else {
                        log::warn!(
                            "{}:{}: Attmepted to exit the only mode available",
                            file!(),
                            line!()
                        );
                        continue;
                    }
                }
                EnterMode(kind) | ChangeMode(kind) if !self.allowed_modes.contains(kind) => {
                    outs.push(E::error(Error::IllegalMode(kind)));
                    return outs;
                }
                EnterMode(kind) => {
                    self.mode_stack.push(kind.xinto());
                    continue;
                }
                ChangeMode(kind) => {
                    self.mode_stack.pop();
                    self.mode_stack.push(kind.xinto());
                    continue;
                }
            };

            let style = self.cursor_style();
            let res = self.executor.execute(cmd, style);
            let is_err = res.is_error();

            outs.push(res);
            if is_err {
                return outs;
            }
        }

        return outs;
    }

    /// Provides immutable access to the internal executor
    pub fn executor(&self) -> &E {
        &self.executor
    }

    /// Provides mutable access to the internal executor
    pub fn executor_mut(&mut self) -> &mut E {
        &mut self.executor
    }

    pub fn expecting_input(&self) -> bool {
        self.current().expecting_input()
    }

    pub fn try_name_with_width(&self) -> Option<(&'static str, usize)> {
        self.current().try_name().map(|s| (s, s.len()))
    }

    pub fn cursor_style(&self) -> CursorStyle {
        self.current().cursor_style()
    }

    fn current(&self) -> &Modes<Meta> {
        self.mode_stack.last().unwrap()
    }
}
