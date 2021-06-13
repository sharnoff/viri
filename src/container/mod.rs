use crate::macros::init;
use crate::term;
use crate::view::{path_view, OutputSignal, SplashView, View};
use crate::{TermPos, TermSize};
use clap::{Arg, ArgMatches};
use std::sync::Arc;
use tokio::stream::{Stream, StreamExt};
use tokio::sync::Notify;

pub mod bottom_bar;
mod config;
pub mod paint;
pub mod signal;

use bottom_bar::BBCtx;
use paint::{Buffer, Extract};
use signal::Signal;

pub use bottom_bar::BottomBar;
pub use config::Config;
pub use paint::Painter;
pub use signal::{make_event_stream, Input};

// Currently, we don't have any initialization that needs to be done here, but this is kept as a
// placeholder in case we *do* have more at some point.
init!();

/// The primary interface between the event loop and the tree of `View`s
///
/// This type takes [`Signal`]s as input and feeds them to the tree of [`View`]s, before taking the
/// resulting [view signal](OutputSignal) and returning a runtime singal, if any was generated.
pub struct Container {
    // The inner `View` being displayed. This will always be `Some(_)`, but we wrap it in an
    // `Option` so that we can safely move out of it to replace.
    inner: Option<InnerState>,

    // Wrapped in an `Option` for the same reason as `inner`.
    bottom_bar: Option<BottomBar>,
    current_input: String,
    last_error_message: Option<String>,

    refresh: Refresh,

    // The buffer storing the current state of the terminal, so that we can do optimized
    // re-drawing
    //
    // This additionally pairs the current size
    buf: Buffer,
}

enum InnerState {
    Concrete(Box<dyn View>, TermSize),
    WaitingForNonZeroSize(Box<dyn FnOnce(TermSize) -> Box<dyn View>>),
}

enum HandleResult {
    Exit,
    Ok,
}

/// A refresh notifier passed to every [`View`]
///
/// This is used to signal to the [`Container`] that it should perform a refresh, either of the
/// cursor position or the actual content of the buffer.
#[derive(Clone)]
pub struct Refresh {
    content: Arc<Notify>,
    cursor: Arc<Notify>,
}

impl Refresh {
    /// Triggers a full refresh of the displayed content
    fn notify_content(&self) {
        self.content.notify_one();
    }

    /// Triggers a refresh of the position of the cursor on screen
    fn notify_cursor(&self) {
        self.cursor.notify_one();
    }
}

/// Adds the `clap` arguments to base app configuration
///
/// Essentially, because this module is the primary user of a large set of arguments, we want to
/// define them where they're actually used. So this function takes the clap [`App`](clap::App)
/// with some of the system-wide configuration and adds some more specific pieces.
#[rustfmt::skip]
pub fn add_args(app: clap::App) -> clap::App {
    app.arg(Arg::new("FILE")
            .about("Sets the file to open")
            .long_about(concat!(
                "Sets the file or directory to open.\n",
                "If no file is given, a blank file will be used instead.",
                // " When multiple files are",
                // " given, they will be opened in a predetermined, split, consistent layout with all",
                // " files visible.",
            ))
            .index(1)
        )
        /*
        .arg(Arg::new("vertical")
            .long("vert")
            .about("Indicates to open multiple files by splitting vertically")
            .long_about(concat!(
                "Indicates to open multiple files by splitting vertically.\n",
                "This setting only has an effect when opening multiple files at the same time.",
                " I'd only recommend using this in settings where the number of files is known",
                " beforehand, because it *will* give all of the files as a one-deep vertical",
                " split.",
            ))
            .conflicts_with("horizontal")
        )
        .arg(Arg::new("horizontal")
            .long("horiz")
            .about("Indicates to open multiple files by splitting horizontally")
            .long_about(concat!(
                "Indicates to open multiple files by splitting horizontally.\n",
                "This setting only has an effect when opening multiple files at the same time.",
                " I'd only recommend using this in settings where the number of files is known",
                " beforehand, because it *will* give all of the files as a one-deep horizontal",
                " split.",
            ))
            .conflicts_with("vertical")
        )
        */
}

impl Container {
    /// Constructs a new view container with the given program arguments
    ///
    /// This is only really intended to be called once, during program initialization. If there
    /// were any errors, they will be returned as a pre-formatted string with no added trailing
    /// newline.
    pub async fn new(args: &ArgMatches) -> Result<Container, String> {
        let size = term::get_size().map_err(|e| format!("failed to get terminal size: {}", e))?;

        let bottom_bar = BottomBar::new();
        let inner_size = size.vertical_trim(bottom_bar.height(size));

        let refresh = Refresh {
            content: Arc::new(Notify::new()),
            cursor: Arc::new(Notify::new()),
        };

        let refresh_cloned = refresh.clone();

        let view_constructor: Box<dyn FnOnce(_) -> Box<dyn View>> = match args.value_of("FILE") {
            None => Box::new(|_| Box::new(SplashView)),
            Some(file_name) => {
                let file_name = file_name.to_owned();
                Box::new(move |size| path_view(file_name, size, refresh))
            }
        };

        let initial_view = match inner_size {
            Some(size) => InnerState::Concrete(view_constructor(size), size),
            None => InnerState::WaitingForNonZeroSize(view_constructor),
        };

        Ok(Container {
            inner: Some(initial_view),
            bottom_bar: Some(bottom_bar),
            buf: Buffer::new(size),
            current_input: String::new(),
            last_error_message: None,
            refresh: refresh_cloned,
        })
    }

    /// Returns the size of the `Container`
    fn size(&self) -> TermSize {
        self.buf.size()
    }

    /// Returns a reference to the bottom bar of the `Container`
    ///
    /// This is a convenience function to get around the internal representation of an
    /// `Option<BottomBar>`.
    fn bottom_bar(&self) -> &BottomBar {
        self.bottom_bar.as_ref().unwrap()
    }

    /// Runs the container with the given event stream
    ///
    /// This function is primarily used within `main` to hand off control of general program
    /// execution. The function terminates only once the event stream is closed and there is
    /// nothing more to handle.
    pub async fn run_event_loop(mut self, mut events: impl Stream<Item = Signal> + Unpin) {
        self.refresh().await;

        while let Some(sig) = events.next().await {
            match sig {
                Signal::Resize(s) if s != self.size() => self.resize_draw(s).await,
                Signal::Resize(_) => (),
                Signal::Input(inp) => match self.handle(inp).await {
                    HandleResult::Ok => (),
                    HandleResult::Exit => {
                        log::debug!("received `HandleResult::Exit`; returning from event loop");
                        return;
                    }
                },
            }
        }
    }

    /// Resizes the container and refreshes everything on-screen
    async fn resize_draw(&mut self, new_size: TermSize) {
        self.buf = Buffer::new(new_size);

        let inner_size = new_size.vertical_trim(self.bottom_bar().height(new_size));

        match (self.inner.take().unwrap(), inner_size) {
            (inner, None) => {
                self.inner = Some(inner);
                self.display_too_small().await;
            }
            (InnerState::WaitingForNonZeroSize(cons), Some(size)) => {
                self.inner = Some(InnerState::Concrete(cons(size), size));
                self.refresh().await;
            }
            (inner, Some(_)) => {
                self.inner = Some(inner);
                self.refresh().await;
            }
        }
    }

    async fn refresh(&mut self) {
        let size = self.size();

        let mut bottom_bar_painter = self.buf.painter();

        let inner_painter = (size.height())
            .checked_sub(self.bottom_bar.as_ref().unwrap().height(size))
            .and_then(|x| match x {
                0 => None,
                x => Some(x),
            })
            .and_then(|height| bottom_bar_painter.split(Extract::Up(height)).ok());

        // Paint the inner `View`
        if let Some(p) = inner_painter {
            self.inner = match self.inner.take().unwrap() {
                InnerState::WaitingForNonZeroSize(cons) => {
                    Some(InnerState::Concrete(cons(p.size()), p.size()))
                }
                inner @ InnerState::Concrete(_, _) => Some(inner),
            };

            match self.inner.as_mut().unwrap() {
                InnerState::WaitingForNonZeroSize(_) => unreachable!(),
                InnerState::Concrete(view, _size) => view.refresh(p).await,
            }
        }

        // Paint the bottom bar
        self.inner = match self.inner.take().unwrap() {
            inner @ InnerState::WaitingForNonZeroSize(_) => {
                let ctx = BBCtx {
                    bottom_bar: self.bottom_bar.take().unwrap(),
                    attr_provider: crate::config::attr::Nothing,
                };

                let ctx = BottomBar::draw(ctx, bottom_bar_painter).await;
                self.bottom_bar = Some(ctx.bottom_bar);
                Some(inner)
            }
            InnerState::Concrete(view, size) => {
                let ctx = BBCtx {
                    bottom_bar: self.bottom_bar.take().unwrap(),
                    attr_provider: view,
                };

                let ctx = BottomBar::draw(ctx, bottom_bar_painter).await;
                self.bottom_bar = Some(ctx.bottom_bar);
                Some(InnerState::Concrete(ctx.attr_provider, size))
            }
        };

        // After painting everything to the buffer, we finally write the updates to the screen
        let res = match self.buf.draw(tokio::io::stdout()).await {
            e @ Err(_) => e,
            Ok(()) => self.set_cursor().await,
        };

        if let Err(e) = res {
            // If there was an error here, we probably should exit
            let msg = format!("failed to write output: {}", e);
            log::error!("{}: {}", file!(), msg);
            panic!("{}", msg);
        }
    }

    /// Sets the position of the cursor on the screen
    async fn set_cursor(&self) -> tokio::io::Result<()> {
        use crossterm::{cursor::MoveTo, ExecutableCommand};
        use tokio::io::{stdout, AsyncWriteExt};

        let (view, size) = match self.inner.as_ref().unwrap() {
            // If our size is too small, we don't really have a place to put the cursor
            InnerState::WaitingForNonZeroSize(_) => return Ok(()),
            // Otherwise, ask the inner view:
            InnerState::Concrete(view, size) => (view, size),
        };

        // The position of the top-left corner of the bottom bar
        let bb_pos = TermPos {
            row: size.height(),
            col: 0,
        };

        let pos = match view.cursor_pos().await {
            Some(pos) if size.contains(pos) => pos,
            // If the position is too big, it's an error:
            Some(pos) => {
                log::error!(
                    "requested view cursor position {:?} outside size {:?}",
                    pos,
                    size,
                );

                // TODO-FEATURE: @def "feature: cursor-pos-error" v0
                // report_error(
                //     ErrorKind::Internal,
                //     "requested cursor position outside terminal size",
                // );

                return Ok(());
            }
            None => {
                let pos = bb_pos + self.bottom_bar().cursor_pos();

                if !self.size().contains(pos) {
                    log::error!(
                        "requested bottom bar cursor position {:?} outside size {:?}",
                        pos,
                        size,
                    );
                    // TODO-FEATURE - same as above: @req "feature: cursor-pos-error" v0
                    return Ok(());
                }

                pos
            }
        };

        let mut output = <Vec<u8>>::new();
        output.execute(MoveTo(pos.col, pos.row)).unwrap();
        stdout().write(&output).await?;
        Ok(())
    }

    async fn handle(&mut self, input: Input) -> HandleResult {
        match self.inner.take().unwrap() {
            inner @ InnerState::WaitingForNonZeroSize(_) => {
                self.inner = Some(inner);
                log::warn!(
                    "terminal size {:?} too small to handle input {:?}",
                    self.size(),
                    input
                );
                HandleResult::Ok
            }
            InnerState::Concrete(mut view, inner_size) => {
                // Because the input to a `View` is sometimes provided in batches, it may be the
                // case that not all of it is consumed at once. So we loop
                let mut input = Some(input);
                while let Some(inp) = input {
                    let bb = self.bottom_bar.as_mut().unwrap();
                    let (output, new_input) = view.handle(inp, bb).await;
                    input = new_input;
                    match Container::handle_output(view, inner_size, &self.refresh, output).await {
                        Some(new_view) => view = new_view,
                        None => return HandleResult::Exit,
                    }
                }

                self.inner = Some(InnerState::Concrete(view, inner_size));
                HandleResult::Ok
            }
        }
    }

    /// Handles the output from [`View::handle`], returning the new value for the inner [`View`]
    /// - if the we're intending to continue running
    async fn handle_output(
        view: Box<dyn View>,
        inner_size: TermSize,
        // A copy of the `Container`'s refresh signaller
        refresh: &Refresh,
        output: OutputSignal,
    ) -> Option<Box<dyn View>> {
        match output {
            // Replacing the current view is pretty simple - we just return something else
            OutputSignal::ReplaceThis(cons) => Some(cons(inner_size, refresh)),
            // If a 'shift focus' request makes it to the top-level, we don't have anything to do
            //
            // TODO-FEATURE: This could flash the screen or something (maybe output a BEL signal?)
            OutputSignal::ShiftFocus(_, _) => Some(view),
            OutputSignal::Open(_, _) => todo!(),
            OutputSignal::WaitForMore => todo!(),
        }
    }

    async fn display_too_small(&mut self) {
        todo!()
    }
}
