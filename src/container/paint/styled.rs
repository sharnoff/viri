//! Wrapper module for styling and styled content
//
// TODO-DOC - This module needs a *lot* more documentation

use super::{IntoSymbols, Symbol};
use ansi_term::{Color, Style};

// TODO-DOC
pub struct StyledContent<Iter: IntoSymbols> {
    pub segments: Vec<StyledString<Iter>>,
}

pub struct StyledString<Iter: IntoSymbols = String> {
    pub(super) style: Style,
    pub(super) content: Iter,
}

pub trait Styled {
    fn fg(self, color: Color) -> StyledString;
    fn bg(self, color: Color) -> StyledString;
    fn style(self, style: Style) -> StyledString;
}

impl<Iter: IntoSymbols> StyledString<Iter> {
    /// Converts the `StyledString` to use [`Symbol`]s as the backing storage
    ///
    /// This is required for certain methods, like obtaining the [width](StyledString::width) of a
    /// styled string.
    pub fn into_symbols(self) -> StyledString<Vec<Symbol>> {
        StyledString {
            style: self.style,
            content: self.content.into_symbols().collect(),
        }
    }
}

impl StyledString<Vec<Symbol>> {
    /// Returns the width of the string
    ///
    /// Note: This function is only available after converting to using a vector of [`Symbol`]s as
    /// the underlying "string". That can be done easily with the [`into_symbols`] method.
    ///
    /// [`into_symbols`]: StyledString::into_symbols
    pub fn width(&self) -> usize {
        self.content.len()
    }

    /// Trims the `StyledString` so that it's within the required width by removing symbols from
    /// the left.
    fn trim_left_to(mut self, width: usize) -> Self {
        let mut first_included_idx = self.content.len().saturating_sub(width);
        while self.content.first().map(Symbol::is_empty).unwrap_or(false) {
            first_included_idx += 1;
        }

        // TODO-CORRECTNESS: Will we run into out-of-bounds errors if the final value of
        // `first_included_idx` is equal to the length of the array?
        StyledString {
            style: self.style,
            content: self.content.drain(first_included_idx..).collect(),
        }
    }
}

impl StyledContent<Vec<Symbol>> {
    /// Ensures that the content is within the required width by removing symbols from the left
    pub fn trim_left_to(mut self, width: usize) -> Self {
        let mut new_segments = Vec::new();

        // We need to walk backwards through the list of symbols, removing rest once we have enough
        // to fill the width. We'll push to `new_segments` as we go, and then reverse at the end
        let mut width_so_far = 0;
        for segment in self.segments.into_iter().rev() {
            let added_width = width_so_far + segment.width();
            let trim_from_this_segment = (width_so_far + segment.width()).checked_sub(width);

            let trim = match trim_from_this_segment {
                // If there's room for this full segment, add it
                None | Some(0) => {
                    width_so_far += segment.width();
                    new_segments.push(segment);
                    continue;
                }
                Some(t) => t,
            };

            // Otherwise, we want to keep *just* enough of the segment
            new_segments.push(segment.trim_left_to(trim));
            // And then we're done - we've already exhausted available width
            break;
        }

        new_segments.reverse();
        StyledContent {
            segments: new_segments,
        }
    }
}

///////////////////////////////////////
// Boilerplate trait implementations //
///////////////////////////////////////

impl<Iter: IntoSymbols> From<Vec<StyledString<Iter>>> for StyledContent<Iter> {
    fn from(strings: Vec<StyledString<Iter>>) -> Self {
        StyledContent { segments: strings }
    }
}

impl<Iter: IntoSymbols> From<StyledString<Iter>> for StyledContent<Iter> {
    fn from(string: StyledString<Iter>) -> Self {
        StyledContent {
            segments: vec![string],
        }
    }
}

impl<T: Into<StyledString>> Styled for T {
    fn fg(self, color: Color) -> StyledString {
        let mut s = self.into();
        s.style.background = Some(color);
        s
    }

    fn bg(self, color: Color) -> StyledString {
        let mut s = self.into();
        s.style.background = Some(color);
        s
    }

    fn style(self, style: Style) -> StyledString {
        StyledString {
            style,
            ..self.into()
        }
    }
}

impl<Iter: IntoSymbols> From<Iter> for StyledString<Iter> {
    fn from(iter: Iter) -> Self {
        StyledString {
            style: Style::default(),
            content: iter,
        }
    }
}
