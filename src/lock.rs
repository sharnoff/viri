//! Utilities for a unique lock implementation
//!
//! There are two primary types defined here; [`RawLock`] and [`ArcLock`]. The former gives a
//! mid-level locking `RwLock` interface with support for raw reentrant, exclusive locking. The
//! latter provides a deadlock-safe wrapper that is essentially just an `Arc<RawLock<T>>`.
//! [`ArcLock`] should be preferred in nearly all circumstances; usage of [`RawLock`] itself is
//! incredibly easy to get wrong, especially in complex systems.
//!
//! Additionally, a few type definitions surrounding the `RwLock`s provided by `parking_lot` are
//! provided.
//!
//! [`RawLock`]: struct.Lock.html
//! [`ArcLock`]: struct.ArcLock.html

use crate::prelude::*;

use std::cell::UnsafeCell;
use std::fmt::{self, Debug, Formatter};
use std::sync::Arc;
use std::thread::{self, ThreadId};

use lock_api::RawMutex as _;
use parking_lot::{Mutex, RawMutex, RawRwLock};

/// A type identical to `parking_lot`'s `RwLock`
///
/// The type is defined here so that we might also define [read] and [write] guards.
///
/// [`read`]: type.RwLockReadGuard.html
/// [`write`]: type.RwLockWriteGuard.html
pub type RwLock<T> = lock_api::RwLock<RawRwLock, T>;
pub type RwLockReadGuard<'a, T> = lock_api::RwLockReadGuard<'a, RawRwLock, T>;
pub type RwLockWriteGuard<'a, T> = lock_api::RwLockWriteGuard<'a, RawRwLock, T>;

/// A reentrant, manually-lockable `RwLock`
///
/// **Warning:** This type is difficult to use correctly. For a deadlock-safe version, see
/// [`ArcLock`]; for more information, see ["Deadlock Safety"]
///
/// What does the above actually mean? This type exposes a few different operations: [locking] (and
/// [unlocking]), acquring [read locks], and acquiring [write locks]. The semantics are slightly
/// different from the default `RwLock`; the type can be locked, which prevents other threads from
/// acquiring write locks.
///
/// The precise meaning of reentrant in this context should be noted: **Write locks are not
/// reentrant**. The lock is only reentrant in the sense that multiple calls to [`lock`] may be
/// used in a reentrant fashion. When locked, only the thread holding the lock can acquire write
/// lock, though other threads **may still acquire read locks**.
///
/// All calls to `lock` must be matched by an accompanying `unlock`. Failure to do so *will* result
/// in deadlocks.
///
/// ## Deadlock Safety
///
/// It should also be noted that **this lock is easy to use incorrectly**. It is entirely possible
/// to attempt to acquire a write lock while there is already a read lock in use by the current
/// thread. To mitigate this, the following pattern is recommended:
///
/// ```
/// # use self::*;
/// # use std::sync::Arc;
/// // A generic wrapper. We'll write it generically here so that you can specialize it for
/// // individual types
/// struct Wrapper<T> {
///     data: Arc<RawLock<T>>,
/// }
///
/// impl<T> Wrapper<T> {
///     // `lock` and `unlock` take mutable references, so that the borrowing rules enforce that
///     // no functions further up the stack can hold read locks
///     fn lock(&mut self) { self.data.lock() }
///     fn unlock(&mut self) { self.data.unlock() }
///
///     // The same restriction as for `lock` and `unlock` applies here as well
///     fn write(&mut self) -> WriteGuard<T> { self.data.write() }
///
///     // Read access is the only immutable action allowed
///     fn read(&self) -> ReadGuard<T> { self.data.read() }
/// }
/// ```
///
/// This pattern prevents deadlocks resulting from the usage of `RawLock` by preventing individual
/// threads from attmepting to acquire exclusive locks while a read lock is present in the thread.
///
/// The exact pattern above is provided in the form of [`ArcLock`]; it is recommended to use that
/// type instead.
///
/// [locking]: #method.lock
/// [unlocking]: #method.unlock
/// [read locks]: #method.read
/// [write locks]: #method.write
/// [`lock`]: #method.lock
/// [`ArcLock`]: struct.ArcLock.html
pub struct RawLock<T> {
    /// The number of current write locks (or locks by the `lock` method)
    ///
    /// This field may only be written by the thread whose id is equal to that given by `owner`.
    count: UnsafeCell<usize>,

    /// The thread that owns the write locks above
    owner: Mutex<Option<ThreadId>>,

    /// A raw mutex for waiting on write locks
    raw_mux: RawMutex,
    inner: RwLock<T>,
}

// TODO: Are these correct? This is what is provided for `RwLock`.
unsafe impl<T: Send> Send for RawLock<T> {}
unsafe impl<T: Send + Sync> Sync for RawLock<T> {}

/// A RAII structure around shared read access to the internal `RwLock`
///
/// This is created by the [`read`] method on [`Lock`].
///
/// [`read`]: struct.Lock.html#method.read
/// [`Lock`]: struct.Lock.html
pub struct ReadGuard<'a, T> {
    guard: RwLockReadGuard<'a, T>,
}

/// A RAII structure around unique write access to the internal `RwLock`
///
/// This is created by the [`write`] method on [`Lock`].
///
/// [`write`]: struct.Lock.html#method.write
/// [`Lock`]: struct.Lock.html
pub struct WriteGuard<'a, T> {
    lock: &'a RawLock<T>,
    guard: RwLockWriteGuard<'a, T>,
}

impl<T> Drop for WriteGuard<'_, T> {
    fn drop(&mut self) {
        self.lock.unlock();
    }
}

impl<T> RawLock<T> {
    /// Creates a new `Lock` with the given value
    ///
    /// The lock is initialized as unlocked.
    pub fn new(val: T) -> Self {
        Self {
            count: UnsafeCell::new(0),
            owner: Mutex::new(None),
            raw_mux: RawMutex::INIT,
            inner: RwLock::new(val),
        }
    }

    /// Locks the `Lock`
    ///
    /// For more information, refer to the type's documentation.
    pub fn lock(&self) {
        let id = thread::current().id();
        let mut owner_guard = self.owner.lock();

        if owner_guard.is_none() {
            unsafe {
                *self.count.get() = 1;
            }
            *owner_guard = Some(id);
            self.raw_mux.lock();
        } else if *owner_guard == Some(id) {
            let count = unsafe {
                let ptr = self.count.get();
                *ptr += 1;
                *ptr
            };

            if count == 1 {
                self.raw_mux.lock();
            }
        } else {
            drop(owner_guard);

            // FIXME: This is **very** naive
            let mut owner_guard = loop {
                self.raw_mux.lock();
                let owner_guard = self.owner.lock();
                if !owner_guard.is_none() {
                    self.raw_mux.unlock();
                } else {
                    break owner_guard;
                }
            };

            // Once we manage to lock this, we know that we have unique access `owner` and `count`:
            unsafe {
                *self.count.get() = 1;
            }
            *owner_guard = Some(id);
            self.raw_mux.lock();
        }
    }

    /// Unlocks the `Lock`
    ///
    /// For more information, refer to the type's documentation.
    pub fn unlock(&self) {
        // decrement count
        let count = unsafe {
            let ptr = self.count.get();
            *ptr -= 1;
            *ptr
        };

        if count == 0 {
            *self.owner.lock() = None;
            self.raw_mux.unlock();
        }
    }

    /// Acquires a read lock on the underlying `RwLock`
    ///
    /// For more information, refer to the type's documentation.
    pub fn read(&self) -> ReadGuard<T> {
        ReadGuard {
            guard: self.inner.read(),
        }
    }

    /// Acquires a write lock on the underlying `RwLock`
    ///
    /// For more information, refer to the type's documentation.
    pub fn write(&self) -> WriteGuard<T> {
        self.lock();

        WriteGuard {
            lock: self,
            guard: self.inner.write(),
        }
    }
}

impl<T: Debug> Debug for RawLock<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("Lock").field("inner", &self.inner).finish()
    }
}

impl<T> Deref for ReadGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.guard.deref()
    }
}

impl<T> Deref for WriteGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.guard.deref()
    }
}

impl<T> DerefMut for WriteGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        self.guard.deref_mut()
    }
}

/// A deadlock-safe\* reference-counted wrapper around [`RawLock`]
///
/// Because this type is essentially just an `Arc<RawLock<T>>`, cloning will clone the inner `Arc`,
/// not the underlying value protected by the lock.
///
/// ## Notes on deadlock safety
///
/// This type claims to be "deadlock safe". The precise meaning of this is the following: If this
/// type is used in isolation from other synchronization types, deadlocks cannot occur within safe
/// code. This property is due to the mutability requirements of locking and obtaining write access
/// to the inner value.
///
/// The reasoning behind the mutability requirements is described in more detail under the
/// ["Deadlock Safety"] header of the [`RawLock`] documentation.
///
/// [`RawLock`]: struct.RawLock.html
/// ["Deadlock Safety"] struct.RawLock.html#deadlock-safety
#[derive(Debug)]
pub struct ArcLock<T> {
    data: Arc<RawLock<T>>,
}

impl<T> Clone for ArcLock<T> {
    fn clone(&self) -> Self {
        ArcLock {
            data: self.data.clone(),
        }
    }
}

impl<T> ArcLock<T> {
    /// Creates a new `ArcLock` from the given value
    pub fn new(val: T) -> Self {
        Self {
            data: Arc::new(RawLock::new(val)),
        }
    }

    pub fn lock(&mut self) {
        self.data.lock()
    }
    pub fn unlock(&mut self) {
        self.data.unlock()
    }
    pub fn write(&mut self) -> WriteGuard<T> {
        self.data.write()
    }
    pub fn read(&self) -> ReadGuard<T> {
        self.data.read()
    }
}
