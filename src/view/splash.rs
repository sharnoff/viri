//! Wrapper module for the [`SplashView`]

use super::*;
use crate::container::paint::Styled;
use ansi_term::{Color, Style};

/// The loading splash displayed on startup without a file
///
/// Upon receiving any input, this [`View`] immediately asks to replace itself with an empty file
/// to handle the input instead.
pub struct SplashView;

impl_GetAttrAny!(SplashView);

impl View for SplashView {
    #[async_method]
    async fn handle(
        &mut self,
        input: Input,
        bottom_bar: &mut dyn Textual,
    ) -> (OutputSignal, Option<Input>) {
        todo!()
    }

    #[async_method]
    async fn refresh<'a>(&'a mut self, mut painter: Painter<'a>) {
        painter.clear_all();

        const LINES: [(&str, Style); 5] = [
            ("viri - Vi Re-Imagined", Style::new()),
            ("", Style::new()),
            // @req viri-version v0.1.0
            ("v0.1.0", Style::new().fg(Color::Green)),
            ("https://github.com/sharnoff/viri", Style::new()),
            ("by Max Sharnoff", Style::new()),
        ];

        const HEIGHT: u16 = LINES.len() as u16;

        let size = painter.size();
        let start_row = (size.height() / 2).saturating_sub(HEIGHT / 2);

        for (row, (line, style)) in (start_row..).zip(LINES.iter().cloned()) {
            let start_width = (size.width() / 2).saturating_sub((line.len() / 2) as u16);
            let pos = TermPos {
                row,
                col: start_width,
            };

            // The painter requires that all positions given to it are within the correct bounds,
            // and panics if that condition isn't met. Obviously, we don't want that, so we'll
            // check it ourselves.
            if !size.contains(pos) {
                break;
            }

            painter.paint_at(pos, line.style(style).into());
        }
    }

    #[async_method]
    async fn cursor_pos(&self) -> Option<TermPos> {
        // We always return the top-left corner, because the splash view doesn't allow any actual
        // user interaction
        Some(TermPos { row: 0, col: 0 })
    }
}
