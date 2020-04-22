//! Utilities for a special lock used in the `ContentProvider` implementation for `Handle`
//!
//! The primary type defined here is [`Lock`], which provides many different access methods. The
//! locking type is not designed to be particularly efficient; this is an intentional, temporary
//! choice to allow for better ergonomics.
//!
//! [`Lock`]: struct.Lock.hmtl
// FIXME: Ease restrictions on acquiring read locks. Those could be acquired so long as `owner` is
// `None`, and we would only set owner to Some(..) when we acquire a write lock.

use std::cell::UnsafeCell;
use std::fmt::{self, Debug, Formatter};
use std::ops::{Deref, DerefMut};
use std::thread::{self, ThreadId};

use lock_api::RawMutex as _;
use parking_lot::{Mutex, RawMutex, RawRwLock};

pub type RwLock<T> = lock_api::RwLock<RawRwLock, T>;
pub type RwLockReadGuard<'a, T> = lock_api::RwLockReadGuard<'a, RawRwLock, T>;
pub type RwLockWriteGuard<'a, T> = lock_api::RwLockWriteGuard<'a, RawRwLock, T>;

pub struct Lock<T> {
    count: UnsafeCell<usize>,
    owner: Mutex<Option<ThreadId>>,
    raw_mux: RawMutex,
    inner: RwLock<T>,
}

unsafe impl<T> Sync for Lock<T> {}

pub struct ReadGuard<'a, T> {
    lock: &'a Lock<T>,
    guard: RwLockReadGuard<'a, T>,
}

pub struct WriteGuard<'a, T> {
    lock: &'a Lock<T>,
    guard: RwLockWriteGuard<'a, T>,
}

impl<T> Drop for ReadGuard<'_, T> {
    fn drop(&mut self) {
        self.lock.unlock();
    }
}

impl<T> Drop for WriteGuard<'_, T> {
    fn drop(&mut self) {
        self.lock.unlock();
    }
}

impl<T> Lock<T> {
    pub fn new(val: T) -> Self {
        Self {
            count: UnsafeCell::new(0),
            owner: Mutex::new(None),
            raw_mux: RawMutex::INIT,
            inner: RwLock::new(val),
        }
    }

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

    pub fn read(&self) -> ReadGuard<T> {
        self.lock();

        ReadGuard {
            lock: self,
            guard: self.inner.read(),
        }
    }

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
