//! Utilities for manipulating lines of text, encoded in a variety of formats
//!
//! The supported formats are represented by the enum [`ReprKind`]. Note that this is currently
//! just Utf-8.
//!
//! [`ReprKind`]: enum.ReprKind.html

// Reading for later:
//   http://unicode.org/faq/utf_bom.html#BOM
//   https://softwareengineering.stackexchange.com/questions/370088/is-the-bom-optional-for-utf-16-and-utf-32

use crate::utils::OpaqueOption;
use ansi_term::{ANSIStrings, Style};
use std::fmt::{self, Debug, Formatter};
use std::ops::{Bound, Deref, DerefMut, Range, RangeBounds};
use std::sync::{Arc, Mutex};
use unicode_width::UnicodeWidthChar;

mod cache;
pub mod diff;
mod raw;
pub mod sizes;
pub mod utf8;

use cache::Cache;
pub use diff::Diff;
use raw::Raw;
use sizes::Sizes;

pub struct Lines {
    /// The number of spaces used to represent a single tab character
    tabstop: usize,

    /// The encoding of the text
    repr_kind: ReprKind,

    /// The character sequence denoting a newline
    ///
    /// This will either be `\n` or `\r\n`, and is auto-detected depending on the source, if
    /// possible.
    newline: &'static [u8],

    /// A callback to produce styling whenever it must be re-calculated
    ///
    /// If this value is not given, all styling will be
    //
    // TODO: Add a callback for tracking additions/deletions so that we can reduce the size of
    // cache invalidation - the idea being that we're only required to recalculate small regions of
    // syntax highlighting instead of requring that we re-parse the entire rest of the file.
    styler: Option<StylerCallback>,

    /// The internal, stored structures
    ///
    /// This list will always be non-empty
    lines: Vec<InternalLine>,

    /// A cache to make certain procedures significantly less expensive
    cache: Cache,
}

/// A convenience type for referring to the signature of the callback function given to produce
/// styling for a set of lines.
///
/// The function itself takes a [`StyleRequest`], which gives the last styled line and the
/// line that *should* be styled. The output should give *all* of the styling for *all* of the
/// lines between the last styled line and the requested line - excluding the first, but including
/// the last.
///
/// The returned vector should give the styling for each line in turn, starting at the initial line
/// and ending at the requested line. The styling for each line is given by the inner `Vec`, which
/// has the ranges of each style. If the ranges do not exactly cover the byte ranges of the line
/// without overlapping, a panic will be triggered.
///
/// [`StyleRequest`]: struct.StyleRequest.html
// TODO: Return an outer SmallVec here because the vast majority of cases will only be a single
// line.
pub type StylerCallback =
    Box<dyn Send + Sync + Fn(&Lines, StyleRequest) -> Vec<Vec<(Style, Range<usize>)>>>;

/// The set of lines for which styling has been requested
///
/// This is for use in the [`StylerCallback`] function, which will *nearly always* be called with a
/// request for just a single line.
///
/// [`StylerCallback`]: type.StylerCallback.html
pub struct StyleRequest {
    /// The index of the first line that has not been styled - used for cache invalidation.
    ///
    /// This will often be equal to the requested line, though (e.g. when jumping) there are
    /// crucial cases where it will not that must be handled well.
    pub first_todo: usize,

    /// The index of the line for which styling has been requested
    pub requested: usize,
}

/// The internal structure used to represent individual lines
///
/// There's a few things to note here about the various intermediate representations used in the
/// operations on this type.
///
/// Broadly speaking, there are three endpoints: (1) the raw bytes in the file, (2) the raw bytes
/// of the rendered text, and (3) the width - in columns - of segments of the line. The first two
/// of these are stored directly, and we produce the third by a series of passes through [`Sizes`]
/// to convert values.
///
/// In the documentation for the fields of this type, there's a common notion of *logical
/// characters* vs. *displayed characters*. Logical characters represent single characters (or
/// invalid bytes) in the source, whereas displayed characters represent those that are actually
/// shown on-screen. This distinction exists because some logical characters might be displayed as
/// multiple characters - primarily tabs or non-displayable characters. Tabs, for example, are a
/// single logical character, but are displayed as repeated spaces.
///
/// [`Sizes`]: sizes/struct.Sizes.html
#[derive(Debug)]
struct InternalLine {
    /// Goes from logical character indexes (outer) to indexes in the raw bytes (inner)
    raw_bytes: Sizes<()>,

    /// Goes from logical characters in the text (outer) to the characters that they are displayed
    /// as in the rendered text (inner).
    chars: Sizes<()>,

    /// Goes from logical characters (outer) to their widths (in columns) in the rendered text
    /// (inner).
    ///
    /// The width is tracked at this level so that all functions relative to displayed width can be
    /// aligned per-character, instead of allowing the possibility of splitting in the middle of a
    /// logical character.
    widths: Sizes<()>,

    /// Goes from displayed characters (outer) to their indexes in the raw displayed bytes (inner)
    rendered_bytes: Sizes<()>,

    /// Goes from styling (outer) to logical characters (inner).
    ///
    /// This is allowed to not be present, in which case the value will be re-computed on use.
    styling: Mutex<Option<Sizes<Style>>>,

    /// The total *displayed* width of the line, in columns
    total_width: usize,

    /// The text of the line as it should be displayed on-screen, without styling.
    ///
    /// This is given as an `Option` so that `None` may indicate that the text is exactly what's
    /// present in `raw`.
    rendered: Option<String>,

    /// The raw bytes of the line
    ///
    /// For more information about how this is stored, see [`Raw`].
    ///
    /// [`Raw`]: raw/struct.Raw.html
    raw: Raw<u8>,
}

/// An immutable handle on a single line
///
/// This is created through the [`line`] method on [`Lines`].
///
/// [`line`]: struct.Lines.html#method.line
/// [`Lines`]: struct.Lines.html
#[derive(Copy, Clone)]
pub struct Line<D: Deref<Target = Lines>> {
    idx: usize,
    lines: D,
}

/// The types of encodings available for source files
#[derive(Copy, Clone, Debug)]
pub enum ReprKind {
    Utf8,
    // TODO: Add all of:
    // Hex, Utf16LE, Utf32LE, Utf16BE, Utf32BE
}

/// A trait for types that can provide the content of a [buffer]
///
/// This is defined here (and not in `views::buffer`) because of the extra default method
/// implementations provided that require access to the private fields of [`Lines`].
///
/// The default implementations should not be overrident; for the most part, the default
/// implementations are actually the only sensible ones permitted.
///
/// [buffer]: ../views/buffer/struct.ViewBuffer.html
/// [`Lines`]: struct.Lines.html
pub trait ContentProvider: Sized {
    // FIXME: We need some way of providing reentrant locks and (possibly) upgrading locks

    /// A helper type for providing immutable access to the `Lines`
    type Deref<'a>: Deref<Target = Lines>;

    /// A helper type for providing mutable access to the `Lines`
    type DerefMut<'a>: DerefMut<Target = Lines>;

    /// Locks the content, preventing write locks from being acquired from outside the current
    /// thread.
    ///
    /// This must be callable multiple times from the same thread.
    fn lock(&mut self);

    /// Unlocks the content from a corresponding call to `lock`
    fn unlock(&mut self);

    /// Gives immutable access to the inner `Lines`
    ///
    /// Calls to this method must not block on other calls to `get`, but they may block on
    /// `get_mut`. Put simply, this is allowed to acquire a read lock on the content, but read
    /// locks *must* be able to be aliased.
    fn content<'a>(&'a self) -> Self::Deref<'a>;

    /// Gives mutable access to the inner `Lines`
    ///
    /// Calls to this method are allowed to block until other `Deref`s or `DerefMut`s from calls to
    /// `get` or `get_mut` have been dropped. Put simply, this is allowed to acquire a write lock
    /// on the content.
    fn content_mut<'a>(&'a mut self) -> Self::DerefMut<'a>;

    /// Refreshes the content, providing a list of the changes
    fn refresh(&mut self) -> Vec<Diff>;

    ////////////////////////////////////////////////////////////////////////////////
    // Default method implementations                                             //
    //                                                                            //
    // Note: These methods primarily use internal fields and - as such - cannot   //
    // be overwritten in any meaningful way.                                      //
    ////////////////////////////////////////////////////////////////////////////////

    /// Applies the diff, optionally returning an error if it failed
    ///
    /// This is one of the few provided methods where it could make sense to override the default
    /// implementation. Most overridden implementations will make use of the original; this can be
    /// done by explicitly
    ///
    /// The default implementation will panic if given an invalid diff (verified by
    /// [`Diff::is_valid`]), and if the diff is out of bounds of the total size of the data
    /// represented by the `Lines`.
    fn apply_diff(&mut self, mut diff: Diff) -> Result<(), diff::Error> {
        let mut this = self.content_mut();

        if !diff.is_valid() {
            panic!("invalid diff {:?}", diff);
        }

        // The first thing we'll do is to find the line range corresponding to the diff. If the diff
        // ends up including a newline character (or part of it), but none of the following line,
        // we'll actually include that line as well (assuming it exists).

        let (start_line, start_byte_idx, _) = match this.line_idx(diff.diff_idx) {
            Some(tuple) => tuple,
            None => {
                panic!(
                    "diff index {} is out of bounds of `Lines` size",
                    diff.diff_idx
                );
            }
        };

        let (mut end_line, _, end_includes_newline) =
            match this.line_idx(diff.diff_idx + diff.old.len()) {
                Some(tuple) => tuple,
                None => {
                    panic!(
                        "diff index {} is out of bounds of `Lines` size",
                        diff.diff_idx + diff.old.len()
                    );
                }
            };

        if end_includes_newline {
            end_line += 1;
        }

        // add one to make `end_line` exclusive
        end_line += 1;

        let mut lines = this.lines[start_line..end_line].iter();
        let mut replacement = Vec::from(lines.next().unwrap().raw.deref());
        for line in lines {
            replacement.extend_from_slice(this.newline);
            replacement.extend_from_slice(&line.raw);
        }

        // Subtract off the values from the diff, strip unnecessary context
        diff.diff_idx = start_byte_idx;
        if diff.pre_context.len() > diff.diff_idx {
            let len = diff.pre_context.len();
            diff.pre_context = diff.pre_context[len - diff.diff_idx..len].into();
        }

        let diff_end = diff.diff_idx + diff.old.len();
        if diff_end + diff.post_context.len() > replacement.len() {
            diff.post_context = diff.post_context[0..replacement.len() - diff_end].into();
        }

        diff.apply(&mut replacement)?;

        let new_ref = Arc::new(replacement);

        let new_lines: Vec<_> = split_newline(&new_ref, this.newline)
            .into_iter()
            .map(|range| {
                InternalLine::from_arc(new_ref.clone(), range, this.tabstop, this.repr_kind)
            })
            .collect();

        // We keep track of this value so that we can clear all of the styling on subsequent lines.
        // This gives the end of the segment where clearing might not be necessary
        let clear_end = start_line + new_lines.len();

        if new_lines.len() == end_line - start_line {
            this.lines[start_line..end_line].clone_from_slice(&new_lines);
        } else {
            let mut this_lines = Vec::with_capacity(this.lines.len() + new_lines.len());
            this_lines.extend_from_slice(&this.lines[0..start_line]);
            this_lines.extend_from_slice(&new_lines);
            this_lines.extend_from_slice(&this.lines[end_line..]);
            this.lines = this_lines;
        }

        // Cache invalidation: We'll do it for the actual cache, as well as for the individual
        // rendered texts on each line
        this.cache.invalidate_past_line(start_line);
        for (i, line) in (start_line..).zip(&mut this.lines[start_line..]) {
            let mut style_guard = line.styling.lock().unwrap();
            match style_guard.is_some() || i < clear_end {
                true => *style_guard = None,
                // If the styling is `None`, we can stop our cache invalidation early becaues each
                // styled line requires the previous line to be styled as well
                false => break,
            }
        }

        this.cache.resize(this.lines.len());

        Ok(())
    }

    /// Gives access to a single line, given by `idx`
    ///
    /// This function will panic if the index is out of bounds
    fn line<'a>(&'a self, idx: usize) -> Line<Self::Deref<'a>> {
        let content = self.content();
        if idx >= content.lines.len() {
            panic!(
                "index out of bounds: the len is {} but the index is {}",
                content.lines.len(),
                idx
            );
        }

        Line {
            idx,
            lines: content,
        }
    }

    /// Produces an iterator over `Line`s with the given range
    ///
    /// This function will panic with a subtraction overflow if the end of the range is an exclusive
    /// bound equal to zero or will panic if the end of the range is greater than the total number
    /// of lines.
    fn iter<R: RangeBounds<usize>>(&self, range: R) -> Iter<Self> {
        let content = self.content();
        let start = match range.start_bound() {
            Bound::Included(&b) => b,
            Bound::Excluded(&b) => b + 1,
            Bound::Unbounded => 0,
        };

        let end = match range.end_bound() {
            Bound::Included(&b) => b + 1,
            Bound::Excluded(&b) => b,
            Bound::Unbounded => content.lines.len(),
        };

        if end > content.lines.len() {
            panic!(
                "upper bound {} is out of bounds for {} lines",
                end,
                content.lines.len()
            );
        }

        drop(content);

        Iter {
            lines: self,
            start_idx: start,
            end_idx: end,
        }
    }

    /// Returns the number of lines
    ///
    /// This value will always be greater than or equal to 1.
    fn num_lines(&self) -> usize {
        self.content().lines.len()
    }
}

impl ContentProvider for Lines {
    type Deref<'a> = &'a Self;
    type DerefMut<'a> = &'a mut Self;

    fn lock(&mut self) {}
    fn unlock(&mut self) {}

    fn content(&self) -> &Self {
        self
    }

    fn content_mut(&mut self) -> &mut Self {
        self
    }

    fn refresh(&mut self) -> Vec<Diff> {
        Vec::new()
    }
}

fn split_newline(bytes: &[u8], newline: &[u8]) -> Vec<Range<usize>> {
    // TODO: This is currently a very naive algorithm that is only acceptible because the
    // length the byte sequences that we use for newlines will be short.
    //
    // This may also need to change if UTF-16 / UTF-32 don't work with this method.

    let mut line_ranges = Vec::new();
    let mut last_start = 0;
    let mut nl_idx = 0; // index in `newline`

    let len = newline.len();
    for (i, &b) in bytes.iter().enumerate() {
        if nl_idx == len {
            line_ranges.push(last_start..i - len);
            nl_idx = 0;
            last_start = i;
        }

        if b == newline[nl_idx] {
            nl_idx += 1;
        }
    }

    if nl_idx == len {
        // If there's a newline at the end, we actually need to add both lines; one for the first
        // `n - len` bytes, and one for the empty line at the end
        line_ranges.push(last_start..bytes.len() - newline.len());
        line_ranges.push(bytes.len()..bytes.len());
    } else {
        line_ranges.push(last_start..bytes.len());
    }

    line_ranges
}

impl Lines {
    pub fn from_arc(
        bytes: Arc<Vec<u8>>,
        tabstop: usize,
        repr_kind: ReprKind,
        styler: Option<StylerCallback>,
    ) -> Lines {
        let newline = match repr_kind {
            ReprKind::Utf8 => utf8::detect_newline(&bytes).unwrap_or(utf8::DEFAULT_NEWLINE),
        };

        if newline.is_empty() {
            panic!("Given empty newline delimeter in `Lines::from_arc`. This is not allowed");
        }

        // TODO: This is currently a very naive algorithm that is only acceptible because the
        // length the byte sequences that we use for newlines will be short.
        //
        // This may also need to change if UTF-16 / UTF-32 don't work with this method.

        let mut line_ranges = split_newline(&bytes, newline);

        // Most files will have a trailing newline - this handles that
        let last_range = line_ranges.last().unwrap().clone();
        if line_ranges.len() != 1 && last_range.start == last_range.end {
            line_ranges.pop();
        }

        let lines: Vec<_> = line_ranges
            .into_iter()
            .map(|range| InternalLine::from_arc(bytes.clone(), range, tabstop, repr_kind))
            .collect();

        let cache = Cache::new(&lines, newline.len());

        Self {
            tabstop,
            repr_kind,
            newline,
            styler,
            lines,
            cache,
        }
    }

    /// Produces an empty `Lines`
    pub fn empty(tabstop: usize, repr_kind: ReprKind, styler: Option<StylerCallback>) -> Lines {
        let newline = utf8::DEFAULT_NEWLINE;
        let lines = vec![InternalLine::from_bytes(&[], tabstop, repr_kind)];

        let cache = Cache::new(&lines, newline.len());

        Self {
            tabstop,
            repr_kind,
            newline,
            styler,
            lines,
            cache,
        }
    }

    /// Gives the line and byte within that line corresponding to a global byte index
    ///
    /// This function returns a triple consisting of the line index, the byte index within the
    /// line, and whether it is part of the trailing newline. If the third element in the tuple is
    /// true, the given byte index will be out of bounds in the line corresponding to the index
    /// given by the first element.
    ///
    /// The returned value is `None` if the index is out of bounds.
    fn line_idx(&self, byte_idx: usize) -> Option<(usize, usize, bool)> {
        self.cache
            .line_from(byte_idx, &self.lines, self.newline.len())
    }

    /// Gives the total number of bytes represented by the `Lines`
    pub fn total_bytes(&self) -> usize {
        self.cache.total_bytes(&self.lines, self.newline.len())
    }

    /// Produces a range of the bytes of the `Lines`
    ///
    /// This is typically for internal use, but it may be helpful for collecting the entire
    /// contents - for writing to a file, for example.
    ///
    /// If the given range is out of bounds, this function will panic; the total number of bytes is
    /// given by [`total_bytes()`].
    ///
    /// [`total_bytes()`]: #method.total_bytes
    pub fn collect_range(&self, range: Range<usize>) -> Vec<u8> {
        let mut ret = Vec::with_capacity(range.end - range.start);
        self.collect_into(&mut ret, range);
        ret
    }

    /// Collects the entire contents of the `Lines`, optionally terminating it with a newline
    pub fn collect_all(&self, with_newline: bool) -> Vec<u8> {
        let total = self.total_bytes();
        if with_newline {
            let mut ret = Vec::with_capacity(total + self.newline.len());
            self.collect_into(&mut ret, 0..total)
                .extend_from_slice(self.newline);
            ret
        } else {
            self.collect_range(0..total)
        }
    }

    fn collect_into<'a>(&self, ret: &'a mut Vec<u8>, range: Range<usize>) -> &'a mut Vec<u8> {
        if range.start >= range.end {
            return ret;
        } else if range.end > self.total_bytes() {
            panic!(
                "byte index {} is out of bounds of total size {}",
                range.end,
                self.total_bytes()
            );
        }

        let (start_line, start_byte, _) = self.line_idx(range.start).unwrap();
        let (end_line, end_byte, end_includes_newline) = self.line_idx(range.end).unwrap();

        // let mut ret = Vec::with_capacity(range.end - range.start);

        // Note: end_line is inclusive
        for line_idx in start_line..=end_line {
            if line_idx != start_line {
                ret.extend_from_slice(self.newline);
            }

            let line = &self.lines[line_idx];

            let s = match line_idx == start_line {
                true => start_byte,
                false => 0,
            };

            let e = match line_idx == end_line {
                false => line.raw.len(),
                true => line.raw.len().min(end_byte),
            };

            ret.extend_from_slice(&line.raw[s..e]);

            if line_idx == end_line && end_includes_newline {
                ret.extend_from_slice(&self.newline[..(range.end - range.start) - ret.len()]);
            }
        }

        if ret.len() != range.end - range.start {
            panic!("internal error: `collect_range` return value length mismatch");
        }

        ret
    }

    /// Returns the byte index corresponding to the given line and width index
    ///
    /// If either index is out of bounds, this function will panic.
    pub fn byte_index(&self, line_idx: usize, width_idx: usize) -> usize {
        self.line(line_idx).global_byte_index_from_width(width_idx)
    }

    /// Returns the line and character index in the line corresponding to the given byte index
    ///
    /// The byte index must be within the bounds of the total size of the `Lines`, and must
    /// additionally be character-aligned within the returned line. For the fallible version of
    /// this function, see [`try_line_pair_from_byte`].
    ///
    /// [`try_line_pair_from_byte`]: #method.try_line_pair_from_byte
    pub fn line_pair_from_byte(&self, byte_idx: usize) -> (usize, usize) {
        match self.try_line_pair_from_byte(byte_idx) {
            None => panic!(
                "total byte index {} out of bounds for {} bytes",
                byte_idx,
                self.total_bytes()
            ),
            Some((line_idx, Err(byte))) => panic!(
                "total byte index {} misaligned on line {} at byte {}",
                byte_idx, line_idx, byte
            ),
            Some((line_idx, Ok(char_idx))) => (line_idx, char_idx),
        }
    }

    /// A fallible version of [`line_pair_from_byte`]
    ///
    /// There are two modes of failure accounted for here, so they are represented by the nesting
    /// of the `Result` inside an `Option`. An outer value of `None` signifies that the given byte
    /// index was out of bounds of the total number of bytes in the `Lines` (given by
    /// [`total_bytes()`]). An inner value of `Err(...)` signifies that the byte index in the
    /// resulting line was not at a character boundary; in this case, the index of the byte on the
    /// line is returned instead of the character index.
    ///
    /// [`line_pair_from_byte`]: #method.line_pair_from_byte
    /// [`total_bytes()`]: #method.total_bytes
    pub fn try_line_pair_from_byte(
        &self,
        byte_idx: usize,
    ) -> Option<(usize, Result<usize, usize>)> {
        let (line_idx, byte_idx, in_newline) = self.line_idx(byte_idx)?;

        let line = self.line(line_idx);

        if in_newline {
            if byte_idx != line.inner().raw.len() {
                return Some((line_idx, Err(byte_idx)));
            } else {
                return Some((line_idx, Ok(line.num_chars())));
            }
        }

        // TODO: It isn't critical, but this logic should probably be moved into its own method on
        // `Line`; that would allow greater encapsulation (which *is* valuable here)
        let res = line.inner().raw_bytes.try_idx_from_inner(byte_idx);
        if res.round_down.outer != res.round_up.outer {
            return Some((line_idx, Err(byte_idx)));
        }

        Some((line_idx, Ok(res.round_down.outer)))
    }

    /// Produces the diff corresponding to replacing the given byte range with the contents of a
    /// string
    ///
    /// The range is given in byte indices; if they are out of bounds, this function will panic.
    /// The total number of bytes is given by [`total_bytes()`].
    ///
    /// [`total_bytes()`]: #method.total_bytes
    pub fn replace_byte_range(&self, range: Range<usize>, new: &str) -> Diff {
        let new = match self.repr_kind {
            ReprKind::Utf8 => utf8::into_bytes(new),
        };

        Diff {
            pre_context: self.pre_context_before(range.start),
            post_context: self.post_context_from(range.end),
            diff_idx: range.start,
            old: self.collect_range(range),
            new,
        }
    }

    /// Produces the diff corresponding to inserting the string at a certain byte location
    ///
    /// The byte location is in the total length of the `Lines`. If it is out of bounds, this
    /// function will panic - the total number of bytes is given by [`total_bytes()`].
    ///
    /// [`total_bytes()`]: #method.total_bytes
    #[rustfmt::skip]
    pub fn insert_at_byte(&self, byte_idx: usize, insert: &str) -> Diff {
        self.replace_byte_range(byte_idx..byte_idx, insert)
    }

    /// Produces the diff corresponding to deleting the given byte range.
    ///
    /// The range is given in byte indices; if they are out of bounds, this function will panic.
    /// The total number of bytes is given by [`total_bytes()`].
    ///
    /// [`total_bytes()`]: #method.total_bytes
    pub fn delete_byte_range(&self, range: Range<usize>) -> Diff {
        self.replace_byte_range(range, "")
    }

    // panics if the line is out of bounds
    fn bytes_before_line(&self, line_idx: usize) -> usize {
        self.cache
            .bytes_before_line(line_idx, &self.lines, self.newline.len())
    }

    fn pre_context_before(&self, byte_idx: usize) -> Vec<u8> {
        let start_idx = byte_idx.saturating_sub(diff::CTX_LEN);
        self.collect_range(start_idx..byte_idx)
    }

    fn post_context_from(&self, byte_idx: usize) -> Vec<u8> {
        if byte_idx > self.total_bytes() {
            panic!(
                "byte index {} is out of bounds of total number of bytes {}",
                byte_idx,
                self.total_bytes()
            );
        }

        self.collect_range(byte_idx..(byte_idx + diff::CTX_LEN).min(self.total_bytes()))
    }

    /// Ensures that all of the styling - up to `line_idx` are up-to-date. I.e. that `styling` is
    /// not `None`
    fn update_styling(&self, line_idx: usize) {
        // TODO: This can actually be updated by multiple threads at the same time, in which case
        // work will be duplicated. This probably isn't a big deal, but we might want to add just a
        // little bit of checking to ensure that another thread attempting to update the styling as
        // well will block until this is done.

        // We can - in theory - have any number of previous lines to update as well, but the common
        // case will be that we only need to update a single line.
        //
        // Because of this, a linear search is actually a reasonable way to do it.
        //
        // Practically speaking, it doesn't matter that we do a simple linear run through all
        // of the lines. We *could* use a binary search, but updating the styling will often
        // involve parsing, which is significantly more expensive -- and the interface for
        // binary search means that we're highly likely to use it incorrectly
        let start_line = line_idx
            - (self.lines[..line_idx])
                .iter()
                .rev()
                .take_while(|l| l.styling.lock().unwrap().is_none())
                .count();

        match &self.styler {
            None => self.lines[start_line..=line_idx]
                .iter()
                .for_each(|l| *l.styling.lock().unwrap() = Some(Sizes::new())),
            Some(styler) => {
                let request = StyleRequest {
                    first_todo: start_line,
                    requested: line_idx,
                };
                let styles = styler(&self, request)
                    .into_iter()
                    .chain(std::iter::repeat(Vec::new()));

                for (line, ranges) in self.lines[start_line..=line_idx].iter().zip(styles) {
                    // Convert the ranges into a `Sizes`
                    //
                    // The individual ranges are actually given as *byte ranges*, so we need to
                    // convert those to character ranges as they're expected in the
                    // `InternalLine.styling` before we put those into the `Sizes`
                    let mut sizes = Sizes::new();
                    for (style, range) in ranges {
                        let start_group = (line.raw_bytes)
                            .try_idx_from_inner(range.start)
                            .round_down
                            .outer;
                        let end_group = (line.raw_bytes)
                            .try_idx_from_inner(range.end)
                            .round_down
                            .outer;

                        let start_char = line.chars.idx_from_outer(start_group);
                        let end_char = line.chars.idx_from_outer(end_group);

                        let start_byte = line.rendered_bytes.idx_from_outer(start_char);
                        let end_byte = line.rendered_bytes.idx_from_outer(end_char);

                        sizes.append_by_inner_idx(start_byte, end_byte - start_byte, style);
                    }

                    *line.styling.lock().unwrap() = Some(sizes);
                }
            }
        }
    }
}

impl<D: Deref<Target = Lines>> Line<D> {
    /// Gets the internal line corresponding to this one
    fn inner(&self) -> &InternalLine {
        &self.lines.deref().lines[self.idx]
    }

    /// Returns the total width of the line (in columns) as it would be displayed
    ///
    /// Note that this may be distinct both from the length of the underlying array of bytes and
    /// from the number of characters in the line.
    pub fn width(&self) -> usize {
        self.inner().total_width
    }

    /// Returns the total number of characters present in the line
    ///
    /// Note that this may be distinct from the number of characters in the line as it is
    /// *displayed*.
    pub fn num_chars(&self) -> usize {
        if self.width() == 0 {
            0
        } else {
            self.char_idx_from_width(self.width() - 1).0 + 1
        }
    }

    /// Returns the subset of the rendered line given by the range
    ///
    /// All indexes are given in widths
    pub fn display_segment(&self, range: Range<usize>) -> (String, Range<usize>) {
        if self.inner().styling.lock().unwrap().is_none() {
            self.lines.update_styling(self.idx);
        }

        self.inner().display_segment(range, self.lines.tabstop)
    }

    /// Returns the result of rounding the width both left and right to the nearest character
    ///
    /// The first value in the tuple is from rounding to the left (down) and the second is from the
    /// right. If the given width index is greater than [`self.width()`], this function will panic.
    /// Note that this includes lines with width equal to zero.
    ///
    /// [`self.width()`]: #method.width
    pub fn align_width(&self, width_idx: usize) -> (usize, usize) {
        if width_idx >= self.width() {
            panic!(
                "index out of bounds: the width is {} but the index is {}",
                width_idx,
                self.width()
            );
        }

        // Because the width is the inner index here (characters may have variable-length widths),
        // we give the inner indices of either rounding to return the possible width alignments
        let res = self.inner().widths.try_idx_from_inner(width_idx);
        (res.round_down.inner, res.round_up.inner)
    }

    /// Returns the character indexes corresponding to rounding the width to the nearest characters
    ///
    /// While the provided index must be a location given by column of the *displayed* line, the
    /// returned values are character indexes - yet still distinct from bytes.
    ///
    /// The first value in the tuple is from rounding to the left (down) and the second is from the
    /// right. If the given width index is greater than [`self.width()`], this function will panic.
    /// Note that this includes lines with width equal to zero.
    pub fn char_idx_from_width(&self, width_idx: usize) -> (usize, usize) {
        // Because it's used elsewhere, we'll defer this function to the inner InternalLine
        // implementation
        self.inner().char_idx_from_width(width_idx)
    }

    /// Returns the index in the line's *displayed width* corresponding to the nth character
    ///
    /// If the given charactr index is greater than or equal to the total number of characters in
    /// the line, this function will panic. This value is given by the method [`self.num_chars()`].
    /// Note that this still applies if the number of characters is equal to zero.
    ///
    /// [`self.num_chars()`]: #method.num_chars
    pub fn width_idx_from_char(&self, char_idx: usize) -> usize {
        let n_chars = self.num_chars();
        if char_idx > n_chars {
            panic!(
                "character index out of bounds: index {} for {} characters",
                char_idx, n_chars
            );
        }

        self.inner().widths.idx_from_outer(char_idx)
    }

    /// Returns the byte index in the encapsulating `Lines` corresponding to the given width index
    ///
    /// The width index must be well-aligned (see: [`align_width()`]), else this function will
    /// panic.
    ///
    /// [`align_width()`]: #method.align_width
    pub fn global_byte_index_from_width(&self, width_idx: usize) -> usize {
        let before_bytes = self.lines.bytes_before_line(self.idx);
        let char_idx = {
            let (lower, upper) = self.char_idx_from_width(width_idx);
            if lower != upper {
                panic!(
                    "misaligned width index {}; rounds down to character {} but up to {}",
                    width_idx, lower, upper
                );
            }
            lower
        };

        let byte_idx = self.inner().raw_bytes.idx_from_outer(char_idx);

        before_bytes + byte_idx
    }

    /// Produces an iterator over a range of characters, given by their indexes in the width
    ///
    /// If either of the indexes in the width are not aligned on characters, this function will
    /// panic. Note that exclusive bounds are treated as expected - they are exclusive at the
    /// character level, not the width; no additional logic should be necessary on the part of the
    /// caller.
    ///
    /// More information can be found in the [`chars`] method, which returns the same iterator, but
    /// from the character indexes themselves.
    ///
    /// [`chars`]: #method.chars
    pub fn chars_from_width<R: RangeBounds<usize>>(&self, width_range: R) -> Chars<D> {
        // This function just converts the width bounds into character bounds, panicking if they are
        // not aligned, before calling `chars` to handle the actual work.

        // `desc` describes the index. Best to just see how it's used below
        fn to_char_idx<D: Deref<Target = Lines>>(
            this: &Line<D>,
            width_idx: usize,
            desc: &'static str,
        ) -> usize {
            let (round_down, round_up) = this.char_idx_from_width(width_idx);
            if round_down != round_up {
                panic!(
                    "{} is not well-aligned; rounds down to {}, rounds up to {}",
                    desc, round_down, round_up
                );
            }
            round_down
        }

        let start = match width_range.start_bound() {
            Bound::Included(&b) => Bound::Included(to_char_idx(self, b, "starting index")),
            Bound::Excluded(&b) => Bound::Excluded(to_char_idx(self, b, "starting index")),
            Bound::Unbounded => Bound::Unbounded,
        };

        let end = match width_range.end_bound() {
            Bound::Included(&b) => Bound::Included(to_char_idx(self, b, "ending index")),
            Bound::Excluded(&b) => Bound::Excluded(to_char_idx(self, b, "ending index")),
            Bound::Unbounded => Bound::Unbounded,
        };

        // (Bound<T>, Bound<T>) implements RangeBounds in the manner you'd expect
        self.chars((start, end))
    }

    /// Produces an iterator over a range of characters in the line
    ///
    /// The returned iterator is double-ended, and provides items of type `Option<char>` where
    /// `None` is yielded when a character is invalid.
    pub fn chars<R: RangeBounds<usize>>(&self, char_range: R) -> Chars<D> {
        let left_char = match char_range.start_bound() {
            Bound::Included(&b) => b,
            Bound::Excluded(&b) => b + 1,
            Bound::Unbounded => 0,
        };

        let right_char = match char_range.end_bound() {
            Bound::Included(&b) => b + 1,
            Bound::Excluded(&b) => b,
            Bound::Unbounded => self.num_chars(),
        };

        Chars {
            line: self,
            left_idx: left_char,
            right_idx: right_char,
        }
    }

    /// Gives access to the raw contents of the line as a string, if it is valid utf8
    pub fn try_as_str(&self) -> Option<&str> {
        std::str::from_utf8(&self.inner().raw).ok()
    }
}

impl InternalLine {
    fn from_arc(
        arc: Arc<Vec<u8>>,
        range: Range<usize>,
        tabstop: usize,
        repr_kind: ReprKind,
    ) -> Self {
        let mut line = InternalLine {
            raw_bytes: Sizes::new(),
            rendered_bytes: Sizes::new(),
            chars: Sizes::new(),
            widths: Sizes::new(),
            styling: Mutex::new(None),
            total_width: 0,
            rendered: None,
            raw: Raw::from_range(arc, range),
        };

        line.recompute(tabstop, repr_kind);
        line
    }

    // Creates a new line from the bytes
    //
    // It is assumed that `bytes` will contain no newline characters.
    fn from_bytes(bytes: &[u8], tabstop: usize, repr_kind: ReprKind) -> Self {
        let mut line = InternalLine {
            raw_bytes: Sizes::new(),
            rendered_bytes: Sizes::new(),
            chars: Sizes::new(),
            widths: Sizes::new(),
            styling: Mutex::new(None),
            total_width: 0,
            rendered: None,
            raw: Raw::from(Vec::from(bytes)),
        };

        line.recompute(tabstop, repr_kind);
        line
    }

    /// (Re-)Computes the various additional information stored alongside the line, with the
    /// notable exception of styling.
    fn recompute(&mut self, tabstop: usize, repr_kind: ReprKind) {
        match repr_kind {
            ReprKind::Utf8 => self.recompute_utf8(tabstop),
        }
    }

    // A version of `compute_sizes` specialized to utf8
    fn recompute_utf8(&mut self, tabstop: usize) {
        let mut rendered: Option<String> = None;
        let mut raw_bytes = Sizes::new();
        let mut chars = Sizes::new();
        let mut widths = Sizes::new();
        let mut rendered_bytes = Sizes::new();

        // We're going to iteratively read bytes from the internal buffer.
        // * `idx`          -> our byte index in `self.raw`.
        // * `rendered_idx` -> our byte index in the rendered string.
        // * `char_count`   -> the number of characters (from raw) we've seen
        // * `width`        -> our index in the rendered width
        let mut idx = 0_usize;
        let mut rendered_idx = 0_usize;
        let mut char_count = 0_usize;
        let mut current_width = 0_usize;

        while idx < self.raw.len() {
            let parse_res = utf8::try_next_utf8(&self.raw[idx..]);
            let consumed = match parse_res {
                Ok((_, consumed)) => consumed,
                Err(_) => 1,
            };

            if consumed != 1 {
                raw_bytes.append_by_inner_idx(idx, consumed, ());
            }

            match char_display(tabstop, current_width, parse_res.map(|(c, _)| c)) {
                CharFormat::Normal(c) => {
                    if let Some(r) = rendered.as_mut() {
                        r.push(c);
                    }

                    let width = c.width().unwrap();
                    assert!(width != 0);

                    if width != 1 {
                        widths.append_by_inner_idx(char_count, width, ());
                    }

                    if consumed != 1 {
                        rendered_bytes.append_by_inner_idx(rendered_idx, consumed, ());
                    }

                    rendered_idx += consumed;
                    current_width += width;
                }
                CharFormat::StrLit(s) => {
                    let rendered_ref = match rendered.as_mut() {
                        Some(r) => r,
                        None => {
                            // Create the rendered string if it hasn't been made already.
                            //
                            // This is safe to unwrap because we have already validated
                            // it up to this point as being utf8
                            let s = std::str::from_utf8(&self.raw[..idx]).unwrap();
                            let r = String::from(s);
                            // Store the string in the outer scope
                            rendered = Some(r);
                            rendered.as_mut().unwrap()
                        }
                    };

                    rendered_ref.push_str(s.as_ref());

                    // No need to add to `rendered_bytes` because `StrLit` will always return ascii
                    // strings

                    widths.append_by_inner_idx(current_width, s.len(), ());
                    chars.append_by_outer_idx(char_count, s.len(), ());
                    rendered_idx += s.len();
                    current_width += s.len();
                }
            }

            char_count += 1;
            idx += consumed;
        }

        self.rendered = rendered;
        self.raw_bytes = raw_bytes;
        self.chars = chars;
        self.widths = widths;
        self.rendered_bytes = rendered_bytes;
        self.total_width = current_width;
    }

    // This method is described more extensively in the documentation for the public-facing verion
    // provided by `Line`
    //
    // A note on semantics: If the given range is empty (or if there is nothing to display), the
    // returned range sets both values equal to the end of the original range.
    fn display_segment(&self, mut range: Range<usize>, tabstop: usize) -> (String, Range<usize>) {
        if range.start >= self.total_width {
            // See the semantics note above.
            return (String::new(), (range.end..range.end));
        }

        // Get some initial values that we'll use later out of the way.
        let rendered: &str = match self.rendered.as_ref() {
            None => unsafe { std::str::from_utf8_unchecked(&self.raw) },
            Some(s) => &s,
        };
        let style_guard = self.styling.lock().unwrap();
        let styling = style_guard.as_ref().unwrap();

        // Clamp the high value of the range so that we stay within our indexes. We'll keep the
        // initial value for later.
        let init_end = range.end;
        range.end = range.end.min(self.total_width);

        // search for start/end index
        let (start_width, start_group) =
            self.widths.try_idx_from_inner(range.start).round_up.tuple();
        let (end_width, end_group) = self.widths.try_idx_from_inner(range.end).round_down.tuple();

        // Now, find whether they're represented by multiple characters
        let start_char = self.chars.idx_from_outer(start_group);
        let end_char = self.chars.idx_from_outer(end_group);

        if start_char >= end_char {
            // See the note on semantics above the function definition
            return (String::new(), init_end..init_end);
        }

        let start_byte = self.rendered_bytes.idx_from_outer(start_char);
        let end_byte = self.rendered_bytes.idx_from_outer(end_char);

        // And now we'll produce the final output with styling on the line
        let mut style_regions = Vec::new();
        for (range, opt_style) in styling.inner_regions(start_byte..end_byte) {
            let style = opt_style.unwrap_or_default();
            style_regions.push(style.paint(&rendered[range]));
        }

        let segment = ANSIStrings(&style_regions).to_string();

        (segment, start_width..end_width)
    }

    // The semantics of this function are described where it is publicly exposed.
    // Please refer to the method on `Line` with the same name
    fn char_idx_from_width(&self, width_idx: usize) -> (usize, usize) {
        if width_idx > self.total_width {
            panic!(
                "index out of bounds: the width is {} but the index is {}",
                self.total_width, width_idx
            );
        }

        // Because we want to return the character indices and characters are the *outer* indexing
        // scheme (because characters can have variable-length width), we get the pair of outer
        // indices from either rounding direction.
        let res = self.widths.try_idx_from_inner(width_idx);
        (res.round_down.outer, res.round_up.outer)
    }
}

// A helper function used as part of the routine to render lines
fn char_display(tabstop: usize, current_width: usize, result: Result<char, u8>) -> CharFormat {
    match result {
        Ok(c) => {
            if let Some(w) = c.width() {
                // Some unicode characters are zero-width, and being able to handle those correctly
                // is (currently) outside the scope of this editor.
                if w != 0 {
                    return CharFormat::Normal(c);
                }
            }

            match c {
                '\t' => {
                    let tab_width = match current_width % tabstop {
                        0 => tabstop,
                        w => w,
                    };

                    CharFormat::StrLit((&" ").repeat(tab_width))
                }
                // TODO: Add more support for other characters
                _ => {
                    // If we can't recognize the character, a simple escape sequence should suffice
                    // for now.
                    //
                    // TODO: make displaying this prettier, possibly more performant. The default
                    // formatter may not be all that quick.
                    let s = format!("{:#x}", c as u32);
                    // This gets us something like: "0x236a", which we then convert to a nice
                    // unicode format with:
                    CharFormat::StrLit(format!("<U+{}>", &s[2..]))
                }
            }
        }
        Err(byte) => CharFormat::StrLit(format!("<{:#x}>", byte)),
    }
}

// An internal type used for constructing the metadata required by InternalLine
enum CharFormat {
    /// A character that may be displayed as-is
    Normal(char),
    /// The substitution for a character that *cannot* be directly displayed, alongside what should
    /// be displayed with it. The string here *must* be ASCII.
    StrLit(String),
}

/// An iterator over lines
///
/// This is produced by the [`iter()`] method on [`ContentProvider`s].
///
/// [`iter()`]: struct.ContentProvider.html#method.iter
/// [`ContentProvider`s]: trait.ContentProvider.html
#[derive(Debug)]
pub struct Iter<'a, P: 'a + ContentProvider> {
    lines: &'a P,
    start_idx: usize,
    end_idx: usize,
}

impl<'a, P: 'a + ContentProvider> Iterator for Iter<'a, P> {
    type Item = Line<P::Deref<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start_idx >= self.end_idx {
            return None;
        }

        let line = self.lines.line(self.start_idx);
        self.start_idx += 1;
        Some(line)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.end_idx.saturating_sub(self.start_idx);
        (size, Some(size))
    }
}

impl<'a, P: 'a + ContentProvider> DoubleEndedIterator for Iter<'a, P> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start_idx >= self.end_idx {
            return None;
        }

        let line = self.lines.line(self.end_idx - 1);
        self.end_idx -= 1;
        Some(line)
    }
}

impl<'a, P: 'a + ContentProvider> ExactSizeIterator for Iter<'a, P> {}

/// An iterator over the characters in a line
pub struct Chars<'a, D: 'a + Deref<Target = Lines>> {
    line: &'a Line<D>,
    // The left *character* index
    left_idx: usize,
    // The right *character* index
    right_idx: usize,
}

// A note:
// The current implementation is naive. It could be greatly improved by directly using the `Sizes`
// given in the `InternalLine`. It could also be improved by allowing `Sizes` to cache accessed
// locations, which is perhaps the better of the two approaches (even though it does not provide as
// much of a *guaranteed* improvement, the average case will still be better here - and will likely
// improve elsewhere as well).
impl<'a, D: Deref<Target = Lines>> Iterator for Chars<'a, D> {
    // returns the character index along with the character
    type Item = (usize, Option<char>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.left_idx >= self.right_idx {
            return None;
        }

        let byte_idx = self.line.inner().raw_bytes.idx_from_outer(self.left_idx);
        self.left_idx += 1;
        let res = match self.line.lines.repr_kind {
            ReprKind::Utf8 => utf8::try_next_utf8(&self.line.inner().raw[byte_idx..]),
        };

        Some((self.left_idx - 1, res.map(|(c, _)| c).ok()))
    }
}

impl<'a, D: Deref<Target = Lines>> DoubleEndedIterator for Chars<'a, D> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.left_idx >= self.right_idx {
            return None;
        }

        let byte_idx = self
            .line
            .inner()
            .raw_bytes
            .idx_from_outer(self.right_idx - 1);
        self.right_idx -= 1;
        let res = match self.line.lines.repr_kind {
            ReprKind::Utf8 => utf8::try_next_utf8(&self.line.inner().raw[byte_idx..]),
        };

        Some((self.right_idx, res.map(|(c, _)| c).ok()))
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Boilerplate implementations                                                                    //
////////////////////////////////////////////////////////////////////////////////////////////////////

impl Debug for Lines {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        fmt.debug_struct("Lines")
            .field("tabtop", &self.tabstop)
            .field("repr_kind", &self.repr_kind)
            .field("newline", &self.newline)
            .field("styler", &OpaqueOption::from(&self.styler))
            .field("lines", &self.lines)
            .field("cache", &self.cache)
            .finish()
    }
}

impl<D: Deref<Target = Lines>> Debug for Line<D> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("Line")
            .field("idx", &self.idx)
            .field("inner", self.inner())
            .finish()
    }
}

impl Clone for InternalLine {
    fn clone(&self) -> Self {
        let styling = self.styling.lock().unwrap().clone();

        InternalLine {
            raw_bytes: self.raw_bytes.clone(),
            rendered_bytes: self.rendered_bytes.clone(),
            chars: self.chars.clone(),
            widths: self.widths.clone(),
            styling: Mutex::new(styling),
            total_width: self.total_width.clone(),
            rendered: self.rendered.clone(),
            raw: self.raw.clone(),
        }
    }
}
