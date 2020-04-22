//! An helper module for interfacing with the filesystem and tracking changes
//!
//! This module provides the [`Handle`] type, which is used in the implementation of [`FileView`] to
//! keep changes to the same file from multiple `FileView`s separate (and therefore separately
//! undo-able).
//!
//! This works by storing all files that have been opened during the session in a global registry
//! (`REGISTRY`) and giving each `FileView` a unique identifier to use for edits to a file.
//!
//! [`Handle`]: struct.Handle.html
//! [`FileView`]: ../struct.FileView.html

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

use crate::text::diff;
use crate::text::{ContentProvider, Diff, Lines, ReprKind};

use super::lock::{Lock, ReadGuard, WriteGuard};

use lazy_static::lazy_static;
use parking_lot::RwLock;

lazy_static! {
    /// A global registry to store all of the files that have been opened during this session
    ///
    /// The files are keyed by their absolute, canonicalized paths (if available)
    static ref REGISTRY: RwLock<HashMap<Locator, Arc<Lock<File>>>> = RwLock::new(HashMap::new());
}

const EXTERN_HANDLE_ID: HandleId = HandleId(0);
// NEXT_HANDLE_ID starts at 1 because we represent all external handles with the value 0
static NEXT_HANDLE_ID: AtomicU64 = AtomicU64::new(EXTERN_HANDLE_ID.0 + 1);
static NEXT_LOCAL_ID: AtomicU64 = AtomicU64::new(0);

/// A wrapper type for a handle on a file
///
/// All methods are defined on this type (instead of the inner [`Arc<Lock<File>>`]) so that direct
/// file management can be limited to this module.
///
/// [`Arc<Lock<File>>`]: struct.File.html
// TODO: We'll need to keep track of which diffs have been seen by the handle yet and which
// haven't.
#[derive(Debug)]
pub struct Handle {
    /// The actual file
    ///
    /// When the containing `Handle` is dropped, the `n_handles` field of the file will be
    /// decremented.
    file: Arc<Lock<File>>,

    /// A unique identifier to track changes by
    id: HandleId,
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

    /// A unique identifier to track diffs on this file
    ///
    /// Note that this is distinct from the number of diffs, as that may be
    next_diff_id: u64,

    /// All of the currently applied diffs to the original file with the ID of the handle that made
    /// the change
    ///
    /// A handle id of `None` corresponds to an external change to the file (e.g. running a
    /// formatter).
    diffs: Vec<(Diff, Option<HandleId>)>,

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

/// A locator represents a unique identifier for a
///
/// This is used as the key for the global registry.
// This will eventually also include external files for collaborative editing
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
enum Locator {
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
    pub fn blank(id: LocalId) -> Handle {
        let locator = Locator::Local(id);
        let handle_id = gen_handle_id();

        if let Some(arc_handle) = REGISTRY.read().get(&locator) {
            return Handle {
                file: arc_handle.clone(),
                id: handle_id,
            };
        }

        // These are here for now, until we allow setting them independently via some sort of
        // config. The only issue is that we'll need to support viewing the same file under
        // multiple encodings at the same time. (Which is a good feature to have)
        const TABSTOP: usize = 4;
        const REPR_KIND: ReprKind = ReprKind::Utf8;

        Handle {
            file: Arc::new(Lock::new(File {
                locator,
                content: Lines::from_bytes(&[], TABSTOP, REPR_KIND),
                n_handles: 1,
                unsaved: false,
                next_diff_id: 0,
                diffs: Vec::new(),
                last_write: SystemTime::now(),
            })),
            id: handle_id,
        }
    }

    pub fn open<P: AsRef<Path>>(path: P) -> io::Result<Handle> {
        let path = make_absolute(path)?;

        // We always create a new id. In the future, we might allow explicit creation of a handle
        // from an Id, but that seems like a very niche use case.
        let id = gen_handle_id();
        let locator = Locator::Path(path.clone());

        if let Some(arc_handle) = REGISTRY.read().get(&locator) {
            return Ok(Handle {
                file: arc_handle.clone(),
                id,
            });
        }

        let mut file = File::open(path)?;
        file.n_handles = 1;

        let handle = Handle {
            file: Arc::new(Lock::new(file)),
            id,
        };

        REGISTRY.write().insert(locator, handle.file.clone());
        Ok(handle)
    }

    /// Returns whether the underlying file currently has unsaved changes
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
    pub fn write(&self) -> Result<(), WriteError> {
        let mut guard = self.file.write();
        guard.write()
    }
}

impl File {
    fn open(path: PathBuf) -> io::Result<Self> {
        let content = fs::read(&path)?;

        // These are here for now, until we allow setting them independently via some sort of
        // config. The only issue is that we'll need to support viewing the same file under
        // multiple encodings at the same time. (Which is a good feature to have)
        const TABSTOP: usize = 4;
        const REPR_KIND: ReprKind = ReprKind::Utf8;

        Ok(File {
            locator: Locator::Path(path),
            content: Lines::from_arc(Arc::new(content), TABSTOP, REPR_KIND),
            n_handles: 0,
            unsaved: false,
            next_diff_id: 0,
            diffs: Vec::new(),
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
        f.write(&self.content.collect_all(true))?;
        f.flush()?;
        Ok(())
    }
}

impl ContentProvider for Handle {
    type Deref<'a> = ContentReadGuard<'a>;
    type DerefMut<'a> = ContentWriteGuard<'a>;
    type RefreshError = io::Error;

    fn lock(&self) {
        self.file.lock();
    }

    fn unlock(&self) {
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

    fn apply_diff(&mut self, diff: Diff) -> Result<(), diff::Error> {
        let mut file = self.file.write();
        let res = file.content.apply_diff(diff.clone());
        if res.is_ok() {
            log::trace!("setting unsaved");
            file.unsaved = true;
            file.diffs.push((diff, Some(self.id.clone())));
        }
        res
    }

    fn refresh(&mut self) -> io::Result<Vec<Diff>> {
        todo!()
    }
}

impl Drop for Handle {
    fn drop(&mut self) {
        let mut file_guard = self.file.write();

        // Decrement the counter, like we said we would
        // -> For more info, see documentation for Handle.file and File.n_handles
        file_guard.n_handles -= 1;
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

impl From<io::Error> for WriteError {
    fn from(err: io::Error) -> Self {
        Self::Io(err)
    }
}
