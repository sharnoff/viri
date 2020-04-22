//! Utilities for a special lock used in the `ContentProvider` implementation for `Handle`
//!
//! The primary type defined here is [`Lock`], which provides multiple different access methods. The
//! locking type is not designed to be particularly efficient; this is an intentional, temporary
//! choice to allow for better ergonomics. For more information, see [the type's documentation].
//!
//! [`Lock`]: struct.Lock.html
//! [the type's documentation]: struct.Lock.html

use std::cell::UnsafeCell;
use std::fmt::{self, Debug, Formatter};
use std::ops::{Deref, DerefMut};
use std::thread::{self, ThreadId};

use lock_api::RawMutex as _;
use parking_lot::{Mutex, RawMutex, RawRwLock};

pub type RwLock<T> = lock_api::RwLock<RawRwLock, T>;
pub type RwLockReadGuard<'a, T> = lock_api::RwLockReadGuard<'a, RawRwLock, T>;
pub type RwLockWriteGuard<'a, T> = lock_api::RwLockWriteGuard<'a, RawRwLock, T>;

/// A reentrant, manually-lockable `RwLock`
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
/// [locking]: #method.lock
/// [unlocking]: #method.unlock
/// [read locks]: #method.read
/// [write locks]: #method.write
/// [`lock`]: #method.lock
pub struct Lock<T> {
    /// The number
    count: UnsafeCell<usize>,
    owner: Mutex<Option<ThreadId>>,
    raw_mux: RawMutex,
    inner: RwLock<T>,
}

// TODO: Are these correct? This is what is provided for `RwLock`.
unsafe impl<T: Send> Send for Lock<T> {}
unsafe impl<T: Send + Sync> Sync for Lock<T> {}

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
    lock: &'a Lock<T>,
    guard: RwLockWriteGuard<'a, T>,
}

impl<T> Drop for WriteGuard<'_, T> {
    fn drop(&mut self) {
        self.lock.unlock();
    }
}

impl<T> Lock<T> {
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

impl<T: Debug> Debug for Lock<T> {
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
