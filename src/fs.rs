//! A wrapper module for standardizing filesystem interaction
//!
//! This type essentially gives drop-in replacements for much of the functionality provided by
//! `tokio`'s and the standard library's `fs` and `path` modules, respectively. We do this so that
//! we can store all paths as absolute, which standardizes our representation.

use crate::macros::{init, require_initialized};
use arc_swap::ArcSwap;
use lazy_static::lazy_static;
use std::borrow::Cow;
use std::env;
use std::ffi::{OsStr, OsString};
use std::fmt::{self, Debug, Formatter};
use std::fs::FileType;
use std::path::{Path as StdPath, PathBuf as StdPathBuf};
use std::process::exit;
use std::sync::Arc;
use tokio::fs;
use tokio::io::Result;
use tokio::stream::{Stream, StreamExt};

pub use tokio::fs::File;

/// A wrapper around a `std::path::PathBuf` with extra guarantees
///
/// This type is exactly equal to a `PathBuf` internally, but it is always guaranteed to be
/// absolute, which allows certain a few neat additional features.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Path(StdPathBuf);

impl Debug for Path {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

lazy_static! {
    /// A separate, infallible current working directory
    ///
    /// We use this instead of what's provided by the OS because the OS-provided functions for
    /// getting the current working directory can produce errors.
    ///
    /// In practice, the standard library's implementation (at least for linux) will never return
    /// an error because of the guarantees provided by `libc::getcwd`, but moving that logic to an
    /// internal value reduces our dependence on that guarantee. Essentially, we can always
    /// guarantee that *our* current working directory is present, but we can't say the same about
    /// what the OS provides.
    static ref CURRENT_WORKING_DIR: ArcSwap<Path> = ArcSwap::new(Arc::new(Path(
        "/error: uninitialized fs module".into()
    )));
}

impl<P: Into<StdPathBuf>> From<P> for Path {
    fn from(path: P) -> Path {
        canonicalize(path.into())
    }
}

// Initialize the core functionality required by this module, aborting if any pieces fail
//
// At time of writing, this only initializes the current working directory.
init! {
    let cwd = match env::current_dir() {
        Ok(path) => path,
        Err(e) => {
            eprintln!("fatal error: failed to get current working directory: {}", e);
            exit(1);
        }
    };

    CURRENT_WORKING_DIR.store(Arc::new(Path(
        cwd,
    )));
}

/// Returns the current working directory
///
/// This function will panic if called before this module has been initalized. This is handled at
/// program startup.
pub fn getcwd() -> Arc<Path> {
    require_initialized!(self);

    CURRENT_WORKING_DIR.load_full()
}

/// An infallible version of [`std::fs::canonicalize`]
///
/// Generally, this is used as a "best effort" version of the standard library's `canonicalize` in
/// order to always guarantee we canonicalize as much as is possible. The main reason we provide a
/// different function is that the standard library's implementation will return an error on
/// attempts to canonicalize a path to a file that has not yet been created. This is especially an
/// issue for an editor.
///
/// Here, we instead canonicalize *as much as possible* of the path so that we always have
/// *something* to return. For example, if we're given a path like `"foo/bar/baz"`, but the
/// directory `"bar"` is actually a symlink to `"qux"` (relative to `"bar"`). Even if it doesn't exist,
/// we still return `"foo/qux/baz"`.
///
/// One final piece to note is that this function will panic if the provided path is empty. This is
/// mostly a safeguard for preventing poisoned filepaths elsewhere in the program.
pub fn canonicalize(path: impl AsRef<StdPath>) -> Path {
    let path = path.as_ref();
    assert!(!path.as_os_str().is_empty());

    // If the path isn't absolute, we'll prepend the current working directory
    let path = if !path.is_absolute() {
        let cwd = getcwd();
        cwd.0.join(path)
    } else {
        path.into()
    };

    // If canonicalizing the path works on the first try, we'll return that
    if let Ok(p) = path.canonicalize() {
        return Path(p);
    }

    // Otherwise, we'll do a best-effort canonicalization by building a new path from the
    // components of the one we're and canonicalizing at each addition.
    //
    // This method isn't quite as fast as it could be, but canonicalizing a path isn't something
    // that needs to be done extremely often, so it doesn't really affect the overal feel of the
    // editor.
    let mut components = path.components();
    let mut path: StdPathBuf = "".into();

    for c in &mut components {
        path.push(c);
        match path.canonicalize() {
            Ok(p) => path = p,
            Err(_) => break,
        }
    }

    // If we ended early, we'll add the rest of the components to the path
    components.for_each(|c| path.push(c));

    // The path should never be empty because it's guaranteed to be absolue
    assert!(!path.as_os_str().is_empty());

    Path(path)
}

impl AsRef<StdPath> for Path {
    fn as_ref(&self) -> &StdPath {
        self.0.as_ref()
    }
}

macro_rules! method {
    (
        $(#[$attr:meta])*
        $vis:vis fn $name:ident (&self $(, $($names:ident: $types:ty),*)?) $(-> $ret_ty:ty)?
    ) => {
        $(#[$attr])*
        $vis fn $name (&self $(, $($names: $types),*)?) $(-> $ret_ty)? {
            self.0.$name($($($names),*)?)
        }
    };

    (
        $(#[$attr:meta])*
        $vis:vis async fn $name:ident (&self $(, $($names:ident: $types:ty),*)?) $(-> $ret_ty:ty)?
    ) => {
        $(#[$attr])*
        $vis async fn $name (&self $(, $($names: $types),*)?) $(-> $ret_ty)? {
            self.0.$name($($($names),*)?).await
        }
    };
}

impl Path {
    method!(pub fn is_dir(&self) -> bool);
    method!(pub fn to_string_lossy(&self) -> Cow<str>);
    method!(pub fn extension(&self) -> Option<&OsStr>);
    method!(pub fn exists(&self) -> bool);

    pub fn parent(&self) -> Option<Path> {
        // We know that the parent path will be canonicalized because the child is as well;
        // therefore we don't need to call `canonicalize` to convert this one.
        self.0.parent().map(|p| Path(StdPathBuf::from(p)))
    }

    pub fn join(&self, tail: impl AsRef<StdPath>) -> Path {
        // TODO-ALG: Joined paths often have few changes; there's a lot that we can shortcut here
        // because we know the receiver will be canonicalized.
        self.0.join(tail).into()
    }
}

/// A wrapper function for [`tokio::fs::read_dir`]
pub async fn read_dir(path: &Path) -> Result<impl Stream<Item = Result<DirEntry>>> {
    let iter = fs::read_dir(path).await?.map(|res| res.map(DirEntry));
    Ok(iter)
}

/// A wrapper function for [`tokio::fs::read`]
pub async fn read(path: &Path) -> Result<Vec<u8>> {
    fs::read(path).await
}

/// A wrapper function for [`tokio::fs::read_to_string`]
pub async fn read_to_string(path: &Path) -> Result<String> {
    fs::read_to_string(path).await
}

/// A wrapper type around [`tokio::fs::DirEntry`] exposing an interface modified to provide only
/// absolute paths
#[derive(Debug)]
pub struct DirEntry(fs::DirEntry);

impl DirEntry {
    method!(pub fn file_name(&self) -> OsString);
    method!(pub async fn file_type(&self) -> Result<FileType>);

    /// Returns the path associated with the entry in the directory
    pub fn path(&self) -> Path {
        self.0.path().into()
    }
}
