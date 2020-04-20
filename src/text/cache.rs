//! A helper module for caching certain search results in `Lines`
//!
//! This modules provides a single export, the [`Cache`] type.
//!
//! [`Cache`]: struct.Cache.html

use std::sync::Mutex;

use super::InternalLine;

#[derive(Debug)]
pub struct Cache {
    inner: Mutex<CacheInner>,
}

#[derive(Debug, Clone)]
struct CacheInner {
    byte_indices: Vec<usize>,
    newline_len: usize,
    valid_before: usize,
}

impl Clone for Cache {
    fn clone(&self) -> Cache {
        Self {
            inner: Mutex::new(self.inner.lock().unwrap().clone()),
        }
    }
}

impl Cache {
    pub(super) fn new(lines: &[InternalLine], newline_len: usize) -> Self {
        if lines.len() == 0 {
            panic!("Attempted to create a cache with lines.len() = 0");
        }

        Cache {
            inner: Mutex::new(CacheInner {
                byte_indices: vec![0; lines.len()],
                newline_len,
                valid_before: 1,
            }),
        }
    }

    pub(super) fn line_from(
        &self,
        byte_idx: usize,
        lines: &[InternalLine],
        newline_len: usize,
    ) -> Option<(usize, usize, bool)> {
        self.inner
            .lock()
            .unwrap()
            .line_from(byte_idx, lines, newline_len)
    }

    pub(super) fn bytes_before_line(
        &self,
        line_idx: usize,
        lines: &[InternalLine],
        newline_len: usize,
    ) -> usize {
        self.inner
            .lock()
            .unwrap()
            .bytes_before_line(line_idx, lines, newline_len)
    }

    pub fn resize(&self, new_len: usize) {
        if new_len == 0 {
            panic!("Attempted to resize cache to zero lines");
        }

        let mut inner = self.inner.lock().unwrap();

        if new_len > inner.byte_indices.len() {
            let mut new = vec![0; new_len];
            new[..inner.byte_indices.len()].copy_from_slice(&inner.byte_indices);
            inner.byte_indices = new;
        } else {
            inner.byte_indices.truncate(new_len);
            inner.valid_before = inner.valid_before.min(new_len);
        }
    }

    pub fn invalidate_past_line(&self, line_idx: usize) {
        let mut inner = self.inner.lock().unwrap();
        inner.valid_before = inner.valid_before.min(line_idx + 1);
    }

    pub(super) fn total_bytes(&self, lines: &[InternalLine], newline_len: usize) -> usize {
        self.inner.lock().unwrap().total_bytes(lines, newline_len)
    }
}

impl CacheInner {
    fn assert_eq_len(&self, lines: &[InternalLine]) {
        if self.byte_indices.len() != lines.len() {
            panic!(
                "cache was not sufficiently updated; len ({}) != lines.len ({})",
                self.byte_indices.len(),
                lines.len()
            );
        }
    }

    fn refresh_newline(&mut self, newline_len: usize) {
        if newline_len == self.newline_len {
            return;
        }

        // We need to update all of the newlines
        //
        // We'll switch based on whether we're increasing or decreasing
        if newline_len > self.newline_len {
            let inc = newline_len - self.newline_len;

            for i in 1..self.valid_before {
                self.byte_indices[i] += inc * i;
            }
        } else {
            let dec = self.newline_len - newline_len;

            for i in 1..self.valid_before {
                self.byte_indices[i] -= dec * i;
            }
        }
    }

    fn line_from(
        &mut self,
        byte_idx: usize,
        lines: &[InternalLine],
        newline_len: usize,
    ) -> Option<(usize, usize, bool)> {
        self.assert_eq_len(lines);
        self.refresh_newline(newline_len);

        // If we've already cached enough bytes, we can directly search for it
        if self.byte_indices[self.valid_before - 1] >= byte_idx {}

        // Otherwise, we need to go through all of the lines past where the cache is currently
        // valid and store their proper values
        //
        // 'i' will denote the current index of `byte_indices` we're filling in
        for i in self.valid_before..lines.len() {
            // 'p' for 'previous index'
            // The subtraction is valid because `i ≥ 1` because `valid_before ≥ 1`
            let p = i - 1;

            self.byte_indices[i] = self.byte_indices[p] + lines[p].raw.len() + newline_len;

            if self.byte_indices[i] > byte_idx {
                // either it was part of the line or it was included in the newline
                let in_newline = self.byte_indices[p] + lines[p].raw.len() <= byte_idx;

                return Some((p, byte_idx - self.byte_indices[p], in_newline));
            } else if self.byte_indices[i] == byte_idx {
                return Some((i, 0, false));
            }
        }

        // If we get to this point, the byte index we were looking for wasn't in any of the lines
        // **before the last line**. It still might be in the last line, though - we'll check for
        // that now
        //
        // 'f' for 'final index'
        let f = lines.len() - 1;
        if self.byte_indices[f] + lines[f].raw.len() <= byte_idx {
            //                                       ^^
            // We allow the value to be equal to `byte_idx` because we'll sometimes have exclusive
            // ranges going through this function - those need to be valid at the edge.
            Some((f, byte_idx - self.byte_indices[f], false))
        } else {
            panic!(
                "Byte index {} greater than total size {}",
                byte_idx,
                self.byte_indices[f] + lines[f].raw.len()
            );
        }
    }

    pub fn bytes_before_line(
        &mut self,
        line_idx: usize,
        lines: &[InternalLine],
        newline_len: usize,
    ) -> usize {
        self.assert_eq_len(lines);
        self.refresh_newline(newline_len);

        if line_idx == 0 {
            return 0;
        }

        // Sets all preceeding indices.
        for i in self.valid_before..(line_idx + 1).min(lines.len()) {
            // 'p' for 'previous index'
            // The subtraction is valid because valid_before is always ≥ 1
            let p = i - 1;
            self.byte_indices[i] = self.byte_indices[p] + lines[p].raw.len() + newline_len;
        }

        if line_idx != lines.len() {
            return self.byte_indices[line_idx];
        }

        self.byte_indices[line_idx - 1] + lines[line_idx - 1].raw.len()
    }

    pub fn total_bytes(&mut self, lines: &[InternalLine], newline_len: usize) -> usize {
        self.bytes_before_line(lines.len(), lines, newline_len)
    }
}
