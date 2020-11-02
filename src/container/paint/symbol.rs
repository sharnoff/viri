//! A wrapper module around [`Symbol`] and the related [`IntoSymbols`] trait

use smallstr::SmallString;
use std::borrow::Cow;
use unicode_segmentation::{Graphemes, UnicodeSegmentation};
use unicode_width::UnicodeWidthChar;

/// A single symbol that may be present inside of a `Cell`
///
/// We can't just use a `char` because some unicode graphemes are made up of multiple characters.
/// The vast majority won't be, so we don't want to allocate memory for every single one of them.
///
/// `Symbol`s have the guarantee that they are always valid once created, so the methods for
/// creating a symbol are intentionally restricted. `Symbol` has the [`from_ascii`] method for
/// individual, simple characters. The only other way to construct a `Symbol` is through the
/// [`IntoSymbols`] trait, which allows a variety of types to produce a sequence of symbols.
///
/// [`from_ascii`]: Symbol::from_ascii
#[derive(Debug, Clone, PartialEq)]
pub struct Symbol(SmallString<[u8; 1]>);

impl Symbol {
    /// Creates a `Symbol` from a single-byte ascii character
    ///
    /// This function will panic if [`byte.is_ascii_graphic`] returns false.
    ///
    /// [`byte.is_ascii_graphic`]: u8::is_ascii_graphic
    pub fn from_ascii(byte: u8) -> Symbol {
        if !byte.is_ascii_graphic() {
            panic!("input {:#} is not an ascii graphic", byte);
        }

        Symbol(SmallString::from_buf([byte]).unwrap())
    }

    /// Returns an "empty" `Symbol`
    ///
    /// This is an internal-only function in order to allow us to represent individually wide
    /// characters with multiple symbols (a starting one, followed by a sequence of empty ones).
    fn empty() -> Symbol {
        Symbol(SmallString::new())
    }

    /// Returns whether the `Symbol` is empty
    pub(super) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Gives the width of the `Symbol` if corresponds to a wide character
    ///
    /// This method is imperfect. There does not seem to be a standard method (at least available
    /// in Rust) for determining the displayed width of a string - **taking multi-character
    /// graphemes into account**. The `unicode-width` crate itself makes this disclaimer:
    ///
    /// > **NOTE:** The computed width values may not match the actual rendered column width. For
    /// > example, the woman scientist emoji comprises of a woman emoji, a zero-width joiner and a
    /// > microscope emoji
    /// >
    /// > ```no_run
    /// > assert_eq!(UnicodeWidthStr::width("👩"), 2); // Woman
    /// > assert_eq!(UnicodeWidthStr::width("🔬"), 2); // Microscope
    /// > assert_eq!(UnicodeWidthStr::width("👩‍🔬"), 4); // Woman scientist
    /// > ```
    ///
    /// So this function is just a best-effort attempt. It was not written by a unicode expert, but
    /// it should hopefully work *well-enough* on most inputs.
    fn is_wide_character(&self) -> Option<usize> {
        // TODO-CORRECTNESS
        //
        // This might have many cases where it's wrong, but it seems to be the case that we can
        // often get the width of a grapheme simply from the width of the first character.
        let width = self.0.chars().next().and_then(UnicodeWidthChar::width)?;
        match width {
            0 | 1 => None,
            _ => Some(width),
        }
    }
}

/// Conversion to an iterator of [`Symbol`]s
///
/// This trait is the primary method for constructing a sequence of `Symbol`s. It should hopefully
/// be fairly self explanatory. It is mostly analagous to the standard library's [`IntoIterator]`,
/// but specialized to `Symbol`s.
///
/// It is implemented for `&str`, `String`, `Cow<str>`, and `Vec<Symbol>`.
///
/// ## Usage
///
/// Standard usage of this trait might look something like:
/// ```
/// let input_string = "abcd";
/// for s in input_string.into_symbols() {
///     println!("{}", s);
/// }
/// ```
pub trait IntoSymbols {
    /// The associated iterator of symbols
    type Iter: Iterator<Item = Symbol>;

    /// Produces the iterator
    fn into_symbols(self) -> Self::Iter;
}

impl<'a> IntoSymbols for &'a str {
    type Iter = CowIter<'a>;

    fn into_symbols(self) -> CowIter<'a> {
        Cow::Borrowed(self).into_symbols()
    }
}

impl IntoSymbols for String {
    type Iter = CowIter<'static>;

    fn into_symbols(self) -> CowIter<'static> {
        let cow: Cow<'static, str> = Cow::Owned(self);
        cow.into_symbols()
    }
}

/// An iterator over the graphemes of a string - borrowed or owned
///
/// While marked as public, this type is not available outside of this module, and hence is only
/// part of the implementation of [`IntoSymbols`] for various types.
pub struct CowIter<'a> {
    // SAFETY: `iter` will reference the value pointed to by `string`, so we need to be careful to
    // drop `iter` before we drop `string`, becase it may be owned.
    //
    // This is why we keep `iter` as an option. We uphold the invariant that `iter` is `Some` all
    // the while this type has not been dropped.
    #[allow(unused)] // unused because it's here to delay being dropped
    string: Cow<'a, str>,
    iter: Option<Graphemes<'a>>,
    // A helper field for producing "empty" symbols when we have a wide grapheme / character
    next_empty: usize,
}

impl Drop for CowIter<'_> {
    fn drop(&mut self) {
        // Uphold the requirements listed above.
        self.iter.take();
    }
}

impl<'a> IntoSymbols for Cow<'a, str> {
    type Iter = CowIter<'a>;

    fn into_symbols(self) -> CowIter<'a> {
        // SAFETY: we extend the lifetime of `iter` so that it can reference `self`.
        let iter: Graphemes = UnicodeSegmentation::graphemes(self.as_ref(), true);
        let iter: Graphemes<'a> = unsafe { std::mem::transmute(iter) };

        CowIter {
            string: self,
            iter: Some(iter),
            next_empty: 0,
        }
    }
}

impl<'a> Iterator for CowIter<'a> {
    type Item = Symbol;

    fn next(&mut self) -> Option<Symbol> {
        if self.next_empty > 0 {
            self.next_empty -= 1;
            return Some(Symbol::empty());
        }

        let next = (self.iter.as_mut().unwrap())
            .next()
            .map(SmallString::from)
            .map(Symbol);

        // We also want to check to see if this is a singular wide character
        if let Some(width) = next.as_ref().and_then(Symbol::is_wide_character) {
            self.next_empty = width - 1;
        }

        next
    }
}

impl IntoSymbols for Vec<Symbol> {
    type Iter = <Self as IntoIterator>::IntoIter;

    fn into_symbols(self) -> Self::Iter {
        self.into_iter()
    }
}

// A couple simple tests to ensure that `CowIter` doesn't do anything funky with its unsafe
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cowiter_normal_use() {
        static CASES: &[(&str, &[&str])] = &[
            ("", &[]),
            ("abcd", &["a", "b", "c", "d"]),
            // Taken directly from the unicode-segmentation documentation:
            // Depending on your editor, this might not render nicely.
            ("a\r\nb🇷🇺🇸🇹", &["a", "\r\n", "b", "🇷🇺", "🇸🇹"]),
        ];

        for (input, output_symbols) in CASES {
            let new_symbols: Vec<_> = input.into_symbols().collect();
            let iter = new_symbols.iter().map(|symbol| &symbol.0 as &str);
            assert!(iter.eq(output_symbols.iter().map(|s| *s)));
        }
    }

    #[test]
    fn cowiter_unused_drop() {
        drop("".into_symbols());
        drop("abcd".into_symbols());
    }
}
