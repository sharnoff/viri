//! A wrapper module for standardizing filesystem interaction
//!
//! This type essentially gives drop-in replacements for much of the functionality provided by the
//! standard library `fs` and `path` modules. We do this so that we can store all paths as absolute,
//! which standardizes our representation.
//!
//! A couple other functions that *aren't* provided by either of the above

use lazy_static::lazy_static;
use std::borrow::Cow;
use std::ffi::{OsStr, OsString};
use std::fmt::{self, Debug, Formatter};
use std::fs::{self, FileType};
use std::path::{Path as StdPath, PathBuf as StdPathBuf};
use std::sync::Mutex;
use std::{env, io};

pub use std::fs::File;

// TODO: Document - key features: owned, always absolute, mirrored methods from
// std::path::Path[Buf]
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Path {
    inner: StdPathBuf,
}

impl Debug for Path {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.inner.fmt(f)
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
    static ref CURRENT_WORKING_DIR: Mutex<Option<StdPathBuf>> = Mutex::new(None);
}

impl<P: Into<StdPathBuf>> From<P> for Path {
    fn from(path: P) -> Path {
        canonicalize(path.into())
    }
}

/// Initializes a few key pieces of functionality required by this module, returning an error if
/// any pieces fail.
///
/// In the event of an error, there are no guarantees made that any of the utilities provided by
/// this module will function correctly. As such, an error here should be immediately reported
/// before terminating the program.
///
/// At time of writing, this only initializes the current working directory.
pub fn init() -> Result<(), io::Error> {
    *CURRENT_WORKING_DIR.lock().unwrap() = Some(env::current_dir()?);
    Ok(())
}

/// Returns the current working directory
///
/// This function will panic if called before [`fs::init`].
///
/// [`fs::init`]: fn.init.html
pub fn getcwd() -> Path {
    let path = (CURRENT_WORKING_DIR.lock())
        .unwrap()
        .as_ref()
        .expect("Failed to get the current working directory; has not been set yet")
        .clone();

    Path { inner: path }
}

/// An infallible version of `std::fs::canonicalize`
///
/// Generally, this is used as a "best effort" version of `fs::canonicalize` in order to always
/// guarantee we canonicalize as much as is possible. The main reason we
/// The main problem here is that the standard
/// library's `canonicalize` will always return an error if the path does not exist.
///
/// Here, we instead canonicalize *as much as possible* of the path so that we always have
/// *something* to return.
///
/// One final piece to note is that this function will panic if the provided path is empty. This is
/// mostly a safeguard for preventing poisoned filepaths elsewhere in the program.
pub fn canonicalize(path: impl AsRef<StdPath>) -> Path {
    let path = path.as_ref();
    assert!(!path.as_os_str().is_empty());

    // If the path isn't absolute, we'll prepend the current working directory
    let path = if !path.is_absolute() {
        let Path { inner: cwd } = getcwd();
        cwd.join(path)
    } else {
        path.into()
    };

    // If canonicalizing the path works on the first try, we'll return that
    if let Ok(p) = path.canonicalize() {
        return Path { inner: p };
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

    Path { inner: path }
}

impl AsRef<StdPath> for Path {
    fn as_ref(&self) -> &StdPath {
        self.inner.as_ref()
    }
}

macro_rules! method {
    (
        $(#[$attr:meta])*
        $vis:vis fn $name:ident (&self $(, $($names:ident: $types:ty),*)?) $(-> $ret_ty:ty)?
    ) => {
        $(#[$attr])*
        $vis fn $name (&self $(, $($names: $types),*)?) $(-> $ret_ty)? {
            self.inner.$name($($($names),*)?)
        }
    };
}

impl Path {
    method!(pub fn is_dir(&self) -> bool);
    method!(pub fn to_string_lossy(&self) -> Cow<str>);
    method!(pub fn extension(&self) -> Option<&OsStr>);

    pub fn parent(&self) -> Option<Path> {
        // We know that the parent path will be canonicalized because the child is as well;
        // therefore we don't need to call `canonicalize` to convert this one.
        self.inner.parent().map(|p| Path {
            inner: StdPathBuf::from(p),
        })
    }

    pub fn join(&self, tail: impl AsRef<StdPath>) -> Path {
        // TODO-ALG: Joined paths often have few changes; there's a lot that we can shortcut here
        // because we know the receiver will be canonicalized.
        self.inner.join(tail).into()
    }
}

/// A wrapper function for `std::fs::read_dir`
pub fn read_dir(path: &Path) -> io::Result<impl Iterator<Item = io::Result<DirEntry>>> {
    fs::read_dir(path).map(|iter| iter.map(|res| res.map(|e| DirEntry { inner: e })))
}

/// A wrapper function for `std::fs::read`
pub fn read(path: &Path) -> io::Result<Vec<u8>> {
    fs::read(&path.inner)
}

/// A wrapper function for `std::fs::read_to_string`
pub fn read_to_string(path: &Path) -> io::Result<String> {
    fs::read_to_string(&path.inner)
}

/// A wrapper type around `std::fs::DirEntry` exposing an interface modified to use
#[derive(Debug)]
pub struct DirEntry {
    inner: fs::DirEntry,
}

impl DirEntry {
    method!(pub fn file_name(&self) -> OsString);
    method!(pub fn file_type(&self) -> io::Result<FileType>);

    pub fn path(&self) -> Path {
        self.inner.path().into()
    }
}
