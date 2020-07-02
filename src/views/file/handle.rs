//! An helper module for interfacing with the filesystem and tracking changes
//!
//! This module provides the [`Handle`] type, which is used in the implementation of [`file::View`] to
//! keep changes to the same file from multiple `file::View`s separate (and therefore separately
//! undo-able).
//!
//! This works by storing all files that have been opened during the session in a global registry
//! (`REGISTRY`) and giving each `file::View` a unique identifier to use for edits to a file.
//!
//! [`Handle`]: struct.Handle.html
//! [`file::View`]: ../struct.View.html

use super::edits::{EditOwner, Edits};
use super::syntax;
use crate::lock::{ArcLock, ReadGuard, RwLock, WriteGuard};
use crate::text::{diff, ContentProvider, Diff, Lines, ReprKind};
use lazy_static::lazy_static;
use std::collections::HashMap;
use std::env::current_dir;
use std::fmt::{self, Debug, Display, Formatter};
use std::fs;
use std::io::{self, Write};
use std::ops::{Deref, DerefMut};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::SystemTime;

lazy_static! {
    /// A global registry to store all of the files that have been opened during this session
    ///
    /// The files are keyed by a `Locator`, which is typically the absolute, canonicalized path of
    /// the file
    static ref REGISTRY: RwLock<HashMap<Locator, ArcLock<File>>> = RwLock::new(HashMap::new());
}

const EXTERN_HANDLE_ID: HandleId = HandleId(0);
// NEXT_HANDLE_ID starts at 1 because we represent all external handles with the value 0
static NEXT_HANDLE_ID: AtomicU64 = AtomicU64::new(EXTERN_HANDLE_ID.0 + 1);
static NEXT_LOCAL_ID: AtomicU64 = AtomicU64::new(0);

/// A wrapper type for a handle on a file
///
/// All methods are defined on this type (instead of the inner [`ArcLock<File>`]) so that direct
/// file management can be limited to this module.
///
/// [`ArcLock<File>`]: struct.File.html
#[derive(Debug)]
pub struct Handle {
    /// The actual file
    ///
    /// When the containing `Handle` is dropped, the `n_handles` field of the file will be
    /// decremented.
    file: ArcLock<File>,

    /// A unique identifier to track changes by
    id: HandleId,

    /// The id of the most recent diff applied at the time of the handle's last interaction with the
    /// file
    ///
    /// Please note that this value has nothing to do with the current set of applied edits; this
    /// is only to track the raw set of changes to the content of the file between calls to
    /// [`refresh`].
    ///
    /// [`refresh`]: #method.refresh
    last_diff_id: DiffId,
}

/// An individual, cached file and its content.
///
/// Note that this does not actively keep a OS-level file handle open.
///
/// This serves as a collected place to store individual changes to a file. This type is never
/// exposed publicly, but it is availble to view here because other documentation mentions it. For
/// more information on what is kept internally, please refer to the source. (It's very friendly!)
pub struct File {
    /// A unique identifier for any file being edited
    ///
    /// For more information, see the documentation for [`Locator`].
    ///
    /// [`Locator`]: enum.Locator.html
    locator: Locator,

    /// The content of the file
    ///
    /// This is cached and updated whenever the file is reloaded. `text::Lines` handles all of the
    /// hard dealing-with-bytes operations so that we don't need to do any of that here.
    content: Lines,

    /// The number of concurrent `View`s editing the file
    ///
    /// This is incremented for every new `Handle` and decremented by their destructors. The number
    /// of currently-active handles is used as a way of determining which undo style to use
    /// (everything together vs. per-Id)
    n_handles: usize,

    /// True whenever the content has changed without being written to the file system
    unsaved: bool,

    /// The set of edits that have been made to the file
    edits: Edits,

    /// A unique identifier to track diffs on this file
    ///
    /// Note that this is distinct from the number of currently-applied diffs, as that value may be
    /// manipulated by undoing and redoing, whereas the Id is guaranteed to be increasing.
    last_diff_id: DiffId,

    /// The complete list of the diffs that have been applied to the file
    ///
    /// This records every single change made to the file, including undoing/redoing diffs. This is
    /// notably distinct from the set of applied diffs, which is explicitly manipulated to provide
    /// undoing.
    diff_history: Vec<(DiffId, Diff, Option<HandleId>)>,

    /// The last time the contents of the file was written to the disc
    ///
    /// Because `SystemTime` is not guaranteed to be monotonically increasing, all logic concerning
    /// this field is isolated; it is only used for determining if the file has been externally
    /// updated.
    last_write: SystemTime,
}

/// Represents an active *local* connection to the current file
///
/// This is just a `u64` for now, but it may be changed at any time.
///
/// `HandleId`s are created via the [`gen_handle_id`] function.
///
/// [`gen_id`]: fn.gen_id.html
// Values here start from 1. This is to allow external edits to be given the HandleId of 0. We
// could have used an enum instead, but this solution involves fewer types and contributes to less
// boilerplate. The only necessary difference is that comments need to explain this in all places
// it's used, but that's okay.
//
// The external edit id is defined (for reference) with the `EXTERN_HANDLE_ID` value.
#[derive(Copy, Debug, PartialEq, Clone, Eq, Hash)]
pub struct HandleId(u64);

/// A locator represents a unique identifier for a file
///
/// This is used as the key for the global registry.
// This will eventually also include external files for collaborative editing
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Locator {
    /// A file's absolute, canonicalized path
    Path(PathBuf),

    /// A "file" that is not attached to any particular filepath
    Local(LocalId),
    // External(ExternId),
}

/// Represents a locally-edited file that is not attached to any particular file
///
/// This is currently a `u64`, but may be changed at any time.
///
/// `LocalId`s are created via the [`gen_local_id`] function.
#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub struct LocalId(u64);

/// Represents a unique identifier for a `Diff` applied to the file
///
/// These are generated with the [`get_inc`] method, which copies the value and increments it.
///
/// [`get_inc`]: #method.inc
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct DiffId(u64);

/// Provides a way of immutably borrowing the file's content
///
/// This type is created by the [`content`] method on a [`Handle`] and requires a read lock until
/// it is dropped. The guard dereferences to a [`Lines`], the underlying representation of the
/// file's content.
///
/// [`content`]: struct.Handle.html#method.content
/// [`Handle`]: struct.Handle.html
/// [`Lines`]: ../../text/struct.Lines.html
pub struct ContentReadGuard<'a> {
    guard: ReadGuard<'a, File>,
}

/// Provides a way of mutably borrowing the file's content
///
/// This type is created by the [`content_mut`] method on a [`Handle`] and requires a write lock on
/// the file until it is dropped. The guard dereferences to a [`Lines`], the underlying
/// representation of the file's content.
///
/// [`content_mut`]: struct.Handle.html#method.content_mut
/// [`Handle`]: struct.Handle.html
/// [`Lines`]: ../../text/struct.Lines.html
pub struct ContentWriteGuard<'a> {
    guard: WriteGuard<'a, File>,
}

/// This represents the class of errors that may result from attempting to write the contents of a
/// file to the filesystem it belongs to.
///
/// There are broadly two categories: errors resulting from filesystem operations (`Io`), and those
/// resulting from the file not belonging to a filesystem we can save to. The latter of these can
/// manifest in multiple ways: either from a file that has not been named (but exists on the local
/// filesystem) or from a file that is being collaboratively edited over a network (and therefore
/// has no concept of saving).
#[derive(Debug)]
pub enum WriteError {
    /// Errors resulting from filesystem operations
    Io(io::Error),

    // /// An error resulting from attempting to write a collaborative network file
    // ///
    // /// These cannot be saved because it is not the client's job to manage that.
    // IsExternal,
    /// The file could not be saved because it has not been named.
    IsUnnamed,
}

/// An internal function for generating a new [`HandleId`]
///
/// [`HandleId`]: struct.HandleId.html
fn gen_handle_id() -> HandleId {
    HandleId(NEXT_HANDLE_ID.fetch_add(1, Ordering::SeqCst))
}

/// A function for generating a new [`LocalId`]
///
/// [`LocalId`]: struct.LocalId.html
pub fn gen_local_id() -> LocalId {
    LocalId(NEXT_LOCAL_ID.fetch_add(1, Ordering::SeqCst))
}

/// A helper function for making paths canonical and absolute
///
/// This is used to standardize all incoming paths so that we can reliably track and synchronize
/// which files are being loaded
fn make_absolute<P: AsRef<Path>>(path: P) -> io::Result<PathBuf> {
    match path.as_ref().is_absolute() {
        true => path.as_ref().canonicalize(),
        false => {
            let cwd = current_dir()?;
            cwd.join(path).canonicalize()
        }
    }
}

impl Handle {
    pub fn blank(id: LocalId, path: Option<&str>) -> Handle {
        let locator = Locator::Local(id);
        let handle_id = gen_handle_id();

        if let Some(file_ref) = REGISTRY.read().get(&locator) {
            let file = file_ref.clone();
            let last_diff_id = file.read().last_diff_id;

            return Handle {
                file,
                id: handle_id,
                last_diff_id,
            };
        }

        // These are here for now, until we allow setting them independently via some sort of
        // config. The only issue is that we'll need to support viewing the same file under
        // multiple encodings at the same time. (Which is a good feature to have)
        const TABSTOP: usize = 4;
        const REPR_KIND: ReprKind = ReprKind::Utf8;

        let styler = path
            // Get the exension
            .and_then(|s| Path::new(s).extension().map(|ext| ext.to_str().unwrap()))
            // TODO: handle the error more gracefully here than just ".ok()"
            .and_then(|ext| syntax::styler_callback(ext).ok());

        Handle {
            file: ArcLock::new(File {
                locator,
                content: Lines::empty(TABSTOP, REPR_KIND, styler),
                n_handles: 1,
                unsaved: false,
                edits: Edits::new(),
                last_diff_id: DiffId(0),
                diff_history: Vec::new(),
                last_write: SystemTime::now(),
            }),
            id: handle_id,
            last_diff_id: DiffId(0),
        }
    }

    pub fn open<P: AsRef<Path>>(path: P) -> io::Result<Handle> {
        let path = make_absolute(path)?;

        // We always create a new id. In the future, we might allow explicit creation of a handle
        // from an Id, but that seems like a very niche use case.
        let id = gen_handle_id();
        let locator = Locator::Path(path.clone());

        if let Some(file_ref) = REGISTRY.read().get(&locator) {
            let file = file_ref.clone();
            let last_diff_id = file.read().last_diff_id;

            return Ok(Handle {
                file,
                id,
                last_diff_id,
            });
        }

        let mut file = File::open(path)?;
        file.n_handles = 1;
        let last_diff_id = file.last_diff_id;

        let handle = Handle {
            file: ArcLock::new(file),
            id,
            last_diff_id,
        };

        REGISTRY.write().insert(locator, handle.file.clone());
        Ok(handle)
    }

    /// Returns whether the underlying file currently has changes that have not been synced with
    /// the filesystem
    pub fn unsaved(&self) -> bool {
        let guard = self.file.read();
        guard.unsaved
    }

    /// Attempts to write the underlying file to the disk, regardless of whether it had been saved
    /// already.
    ///
    /// This will return an error in one of two circumstances: if the file does not correspond to
    /// one in the local filesystem or in the event of an IO error from attempting to write the
    /// file. For more information, see [`WriteError`].
    ///
    /// This function will panic if the internal lock on the file has been poisoned.
    ///
    /// [`WriteError`]: enum.WriteError.html
    pub fn write(&mut self) -> Result<(), WriteError> {
        let mut guard = self.file.write();
        guard.write()
    }

    /// Attempts to undo the last 'n' changes
    ///
    /// More information on undoing is provided in the sibling module [edits]. This function will
    /// produce an additional return of `false` when it is unable to undo *all* of the requested
    /// changes. Note that there may still be changes that were undone.
    ///
    /// [edits]: ../edits/index.html
    pub fn undo(&mut self, n: usize) -> Result<(Vec<Diff>, bool), diff::Error> {
        let mut file = self.file.write();

        let mut ret_diffs = Vec::new();
        for _ in 0..n {
            let diffs = match file.edits.get_undo() {
                Some(diffs) => diffs,
                None => return Ok((ret_diffs, true)),
            };

            ret_diffs.extend_from_slice(&diffs);

            // Attempt to apply the diffs. If any one of these fails, there's a bigger issue that
            // will need to be addressed. There isn't really a good solution here.
            for diff in diffs.into_iter() {
                file.content.apply_diff(diff.clone())?;
                let id = file.last_diff_id.get_inc();
                file.diff_history.push((id, diff, Some(self.id)));
            }

            // We'll unwrap just to validate it
            file.edits.commit_undo().unwrap();
        }

        Ok((ret_diffs, false))
    }

    /// Attempts to redo the 'n' most recently undone changes
    ///
    /// More information on redoing is provided in the sibling module [edits]. This function's
    /// signature is the same as [`undo`]; the semantics implied by the returned values are the
    /// same.
    ///
    /// [edits]: ../edits/index.html
    /// [`undo`]: #method.undo
    pub fn redo(&mut self, n: usize) -> Result<(Vec<Diff>, bool), diff::Error> {
        let mut file = self.file.write();

        let mut ret_diffs = Vec::new();
        for _ in 0..n {
            let diffs = match file.edits.get_redo() {
                Some(diffs) => diffs,
                None => return Ok((ret_diffs, true)),
            };

            ret_diffs.extend_from_slice(&diffs);
            let diffs = diffs.iter().cloned().collect::<Vec<_>>();

            // Attempt to apply the diffs. If any one of these fails, there's a bigger issue that
            // will need to be addressed. There isn't really a good solution here.
            for diff in diffs.into_iter() {
                file.content.apply_diff(diff.clone())?;
                let id = file.last_diff_id.get_inc();
                file.diff_history.push((id, diff, Some(self.id)));
            }

            // We'll unwrap just to validate it
            log::trace!("commit redo: {:?}", file.edits);
            file.edits.commit_redo().unwrap();
            log::trace!("after redo: {:?}", file.edits);
        }

        Ok((ret_diffs, false))
    }

    pub fn start_edit_block(&mut self) {
        self.file.write().edits.start_edit_block()
    }

    pub fn end_edit_block(&mut self) {
        self.file.write().edits.end_edit_block()
    }

    /// Clones the handle. This requires a mutable reference in order to obtain a write lock on the
    /// underlying file's number of handles.
    pub fn clone(&mut self) -> Self {
        let mut guard = self.file.write();
        guard.n_handles += 1;
        drop(guard);

        Self {
            file: self.file.clone(),
            id: gen_handle_id(),
            last_diff_id: self.last_diff_id,
        }
    }

    /// Returns the locator corresponding to the underlying file.
    pub fn locator(&self) -> Locator {
        self.file.read().locator.clone()
    }
}

impl File {
    fn open(path: PathBuf) -> io::Result<File> {
        let content = fs::read(&path)?;

        // These are here for now, until we allow setting them independently via some sort of
        // config. The only issue is that we'll need to support viewing the same file under
        // multiple encodings at the same time. (Which is a good feature to have)
        const TABSTOP: usize = 4;
        const REPR_KIND: ReprKind = ReprKind::Utf8;

        let styler = path
            .extension()
            // TODO: Better error handling here than just ".ok()"
            .and_then(|ext| syntax::styler_callback(ext.to_str()?).ok());

        Ok(File {
            locator: Locator::Path(path),
            content: Lines::from_arc(Arc::new(content), TABSTOP, REPR_KIND, styler),
            n_handles: 0,
            unsaved: false,
            edits: Edits::new(),
            last_diff_id: DiffId(0),
            diff_history: Vec::new(),
            last_write: SystemTime::now(),
            //          ^^^^^^^^^^^^^^^^^ This probably isn't the *correct* value here. What we
            //          actually want is more like what we do in `fs_refresh`
        })
    }

    fn write(&mut self) -> Result<(), WriteError> {
        let path: &Path = match &self.locator {
            Locator::Path(p) => p,
            Locator::Local(_) => return Err(WriteError::IsUnnamed),
        };

        let mut f = fs::File::create(path)?;
        f.write_all(&self.content.collect_all(true))?;
        f.flush()?;
        self.unsaved = false;
        Ok(())
    }
}

impl ContentProvider for Handle {
    type Deref<'a> = ContentReadGuard<'a>;
    type DerefMut<'a> = ContentWriteGuard<'a>;

    fn lock(&mut self) {
        self.file.lock();
    }

    fn unlock(&mut self) {
        self.file.unlock();
    }

    /// Provides immutable access to the content of the file
    ///
    /// This function will panic if the lock on the file has been poisoned, and will block on
    /// acquiring a read lock on the file. For more information, see the documentation for
    /// [`ContentReadGuard`].
    ///
    /// [`ContentReadGuard`]: struct.ContentReadGuard.html
    fn content(&self) -> ContentReadGuard {
        ContentReadGuard {
            guard: self.file.read(),
        }
    }

    /// Provides mutable access to the content of the file
    ///
    /// This function will panic if the lock on the file has been poisoned, and will block on
    /// acquiring a write lock on the file. For more information, see the documentation for
    /// [`ContentWriteGuard`]
    ///
    /// [`ContentWriteGuard`]: struct.ContentWriteGuard.html
    fn content_mut(&mut self) -> ContentWriteGuard {
        ContentWriteGuard {
            guard: self.file.write(),
        }
    }

    /// Basic diff application. Each diff given is treated as a single edit
    fn apply_diff(&mut self, diff: Diff) -> Result<(), diff::Error> {
        let mut file = self.file.write();
        let res = file.content.apply_diff(diff.clone());
        if res.is_ok() {
            file.unsaved = true;
            file.edits
                .make_edit(diff.clone(), EditOwner::Local(self.id));
            let diff_id = file.last_diff_id.get_inc();
            file.diff_history.push((diff_id, diff, Some(self.id)));
            self.last_diff_id = diff_id;
        }
        res
    }

    /// Refreshes the handle, returning all of the diffs that have been applied since the last
    /// interaction with that particular handle.
    fn refresh(&mut self) -> Vec<Diff> {
        let file = self.file.read();
        let idx_in_history = file
            .diff_history
            .binary_search_by_key(&self.last_diff_id, |&(id, _, _)| id)
            .map(|i| i + 1)
            .unwrap_or_else(|i| i);

        if let Some(id) = file.diff_history.last().map(|&(id, _, _)| id) {
            self.last_diff_id = id;
        }

        if idx_in_history < file.diff_history.len() {
            file.diff_history[idx_in_history..]
                .iter()
                .map(|(_, diff, _)| diff)
                .cloned()
                .collect()
        } else {
            Vec::new()
        }
    }
}

impl DiffId {
    /// Increments the value, and returns the new value
    ///
    /// This is intended to be used as the primary way to produce new `DiffId`s. If the number of
    /// `Id`s overflows, this function will panic (this will likely never occur).
    fn get_inc(&mut self) -> Self {
        let DiffId(current) = self;
        let new = match current.checked_add(1) {
            Some(new) => DiffId(new),
            None => panic!("DiffId overflow!"),
        };

        *self = new;
        new
    }
}

////////////////////////////////////////////////////////////////////////////////
// Boilerplate trait implementations                                          //
////////////////////////////////////////////////////////////////////////////////

impl Drop for Handle {
    fn drop(&mut self) {
        let mut file_guard = self.file.write();

        // Decrement the counter, like we said we would
        // -> For more info, see documentation for Handle.file and File.n_handles
        file_guard.n_handles -= 1;
        drop(file_guard);
    }
}

impl Deref for ContentReadGuard<'_> {
    type Target = Lines;

    fn deref(&self) -> &Lines {
        &self.guard.content
    }
}

impl Deref for ContentWriteGuard<'_> {
    type Target = Lines;

    fn deref(&self) -> &Lines {
        &self.guard.content
    }
}

impl DerefMut for ContentWriteGuard<'_> {
    fn deref_mut(&mut self) -> &mut Lines {
        &mut self.guard.content
    }
}

impl Debug for File {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("File")
            .field("locator", &self.locator)
            .field("n_handles", &self.n_handles)
            .field("unsaved", &self.unsaved)
            .field("edits", &self.edits)
            .field("last_diff_id", &self.last_diff_id)
            .field("diff_history", &self.diff_history)
            .field("last_write", &self.last_write)
            .finish()
    }
}

impl Display for WriteError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Io(io_err) => write!(f, "Could not write to file: {}", io_err),
            Self::IsUnnamed => write!(f, "Could not write to file; it is unnamed"),
        }
    }
}

impl Display for Locator {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use Locator::{Local, Path};

        match self {
            Path(p) => write!(f, "{}", p.to_string_lossy()),
            Local(_) => write!(f, "[No Name]"),
        }
    }
}

impl From<io::Error> for WriteError {
    fn from(err: io::Error) -> Self {
        Self::Io(err)
    }
}
