//! Setup and teardown of the runtime environment for the editor
//!
//! The submodule `panic` defines the replacement panic hook we use in order to ensure panic
//! messages are never overwritten, in addition to the enabling and disabling of that system.
//!
//! ## Assumptions
//!
//! There are a few assumptions made about anything running here - they aren't *critical*, but
//! could cause things to be mis-reported (e.g. panics not displaying) if they aren't adhered to.
//! We'll list them out here, so that there's one central place they're formally given.
//!
//! 1. **Functions running outside of a `tokio` task do not panic**
//!
//! Nothing seriously wrong can happen if another thread panics, but there's a chance it won't get
//! reported if it does. This is because the panic handler prints all of the messages (and -
//! crucially - will ignore everything afterwards) once the `tokio` executor is shut down. This
//! isn't a strict requirement of the internal designs of each, but it happens to be how everything
//! is implemented at a high-level. Other threads might not be synchronized with that - especially
//! at shutdown, where panics are more likely to occur - and so it becomes likely that panic
//! messages might be lost.
//!
//! ## Shutdown
//!
//! Shutting down the runtime is a non-trivial task. If we were to use the "normal" way provided
//! directly by `tokio` (essentially: just dropping the executor), we'd immediately kill any tasks
//! that are currently blocked. For lots of things, that's probably okay. There are other things
//! that *really* can't be forcefully ended, so we provide a couple of things to make that nicer.
//!
//! The first piece of the puzzle is [`ShutdownWaiter`], which blocks shutting down until it's been
//! dropped. Blindly blocking shutdown obviously doesn't do us much good, so the second piece is
//! the [`shutdown_notifier`] function, which provides a future that completes only once there's
//! been a request to shut down.
//!
//! Because we *still* wouldn't want to allow these to take forever, there's also a timeout limit -
//! after which we ignore any outstanding [`ShutdownWaiter`]s, report an error,  and shutdown
//! anyways. The length of time we wait for things to finish is controlled by [`SHUTDOWN_TIMEOUT`].
//!
//! #### Shutdown: final notes
//!
//! There's a couple more pieces of information that might be useful. These are all pretty
//! straight-forward, so they're presented as a list:
//!
//! 1. We allow creating new tasks right up until the precise moment we shut down the executor -
//!    i.e. until the moment the timeout expires
//! 2. Attempting to interact with the executor *after* it's been fully shut down gives
//!    [`RuntimeAlreadyShutdown`] as the error.
// TODO-DOC: what else is important to know?

use crate::macros::{init, require_initialized};
use arc_swap::{ArcSwapAny, ArcSwapOption};
use lazy_static::lazy_static;
use std::fmt::{self, Display, Formatter};
use std::future::Future;
use std::sync::{Arc, Weak};
use std::time::Duration;
use tokio::sync::{oneshot, Notify};
use tokio::task::JoinHandle;

mod panic;

struct Executor {
    exec: tokio::runtime::Runtime,
    shutdown_tx: Arc<oneshot::Sender<()>>,
    // We use a receiver so that we can block until all senders have dropped.
    shutdown_rx: oneshot::Receiver<()>,
}

lazy_static! {
    // The async executor
    //
    // This is never exposed directly, but can be accessed through the `spawn` and `try_spawn`
    // methods. The inner executor is removed for shutdown, and so this value will be `None` if
    // shutdown has started.
    static ref EXECUTOR: ArcSwapAny<Option<Arc<Executor>>> = {
        use tokio::runtime::Builder;
        use tokio::sync::oneshot;

        let (tx, rx) = oneshot::channel();

        ArcSwapOption::from(Some(Arc::new(Executor {
            // We explicitly build the executor so that we can ensure it's multithreaded
            exec: Builder::new_multi_thread()
                .thread_name("viri-rt-worker")
                .enable_all()
                .build()
                .expect("failed to build the core executor"),
            shutdown_tx: Arc::new(tx),
            shutdown_rx: rx,
        })))
    };

    // A reference to the actual executor that's guaranteed to always be available - even after
    // we've taken the value out of `EXECUTOR`
    static ref EXECUTOR_REF: Weak<Executor> = {
        Arc::downgrade(EXECUTOR.load().as_ref().unwrap())
    };

    // The global notifier that's used to signal whenever the executor shutdown has begun
    static ref SHUTDOWN_NOTIFIER: Notify = Notify::new();
}

// @def runtime::init v0
init! {
    // There isn't much runtime initialization to do, other than to ensure that the executor has
    // been built before we use it
    lazy_static::initialize(&EXECUTOR);
    lazy_static::initialize(&EXECUTOR_REF);
    // ^ really we only need to initialize this one, but it's nice to have redundancy in case of
    // changes.

    mod panic;
}

/// Spawns a single task on the executor, returning a `JoinHandle` for the task
///
/// The join handle can be safely dropped and the executor will continue attempting to complete it.
///
/// ## Panics
///
/// This function will panic once runtime shutdown has progressed past a certain stage; for a
/// fallible version, use [`try_spawn`].
pub fn spawn<F>(future: F) -> JoinHandle<F::Output>
where
    F: Future + Send + 'static,
    F::Output: Send + 'static,
{
    try_spawn(future).unwrap()
}

/// A fallible version of [`spawn`], returning an error if the runtime has already started shutting
/// down
///
/// Shutting down the runtime requires taking ownership of it. This is the *final* step in full
/// runtime shutdown, and so reaching this point means that any yield to the `tokio` scheduler will
/// cause the future to be immediately dropped.
///
/// To avoid this from happening, you can use a [`ShutdownWaiter`] to request that the runtime not
/// shutdown until you're done. This isn't guaranteed - for more information, see the
/// ["shutdown" section] of `crate::runtime`.
///
/// ["shutdown" section]: crate::runtime#shutdown
pub fn try_spawn<F>(future: F) -> Result<JoinHandle<F::Output>, RuntimeAlreadyShutdown>
where
    F: Future + Send + 'static,
    F::Output: Send + 'static,
{
    require_initialized!(crate::runtime);
    match EXECUTOR_REF.upgrade() {
        Some(e) => Ok(e.exec.spawn(future)),
        None => Err(RuntimeAlreadyShutdown),
    }
}

/// An error from attempting to spawn a future when the runtime has already begun shutdown
#[derive(Copy, Clone, Debug)]
pub struct RuntimeAlreadyShutdown;

impl Display for RuntimeAlreadyShutdown {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("failed to spawn task; runtime shutdown has started")
    }
}

impl std::error::Error for RuntimeAlreadyShutdown {}

// TODO-DOC
pub fn shutdown_notifier() -> &'static Notify {
    todo!()
}

/// The default maximum duration we're willing to wait for things to shut down on their own
///
/// For more information, refer to the [module documentation](self#shutdown).
const SHUTDOWN_TIMEOUT: Duration = Duration::from_millis(500);

/// A guard that keeps the runtime alive
///
/// An instance of this type will prevent the runtime from being shut down, until this is dropped
/// - up to [`SHUTDOWN_TIMEOUT`]. This type is intended to be used in conjunction with the
/// [`shutdown_notifier`], and will provide little value without it. For more information on
/// shutdown, refer to the [module documentation](self#shutdown).
///
/// `ShutdownWaiter`s are created with the [`ShutdownWaiter::new`] method, which may return an
/// error if the runtime shutdown has already begun.
//
// We use a Sender here because a `oneshot::Receiver` will finish blocking once all senders are
// dropped. The receiver that we wait for is in `Executor.shutdown_rx`
struct ShutdownWaiter(Arc<oneshot::Sender<()>>);

lazy_static! {
    static ref WAITERS: () = ();
}

impl ShutdownWaiter {
    /// Creates a new `ShutdownWaiter`, provided that the runtime has not already started shutting
    /// down
    ///
    /// If this function returns an error, it is likely that the runtime will shutdown *very* soon.
    /// There's no guarantees about how long the caller will be allowed to continue executing - no
    /// matter whether it's blocking or not.
    pub fn new() -> Result<ShutdownWaiter, RuntimeAlreadyShutdown> {
        require_initialized!(crate::runtime);

        match EXECUTOR_REF.upgrade() {
            Some(e) => Ok(ShutdownWaiter(e.shutdown_tx.clone())),
            None => Err(RuntimeAlreadyShutdown),
        }
    }

    /// A convenience function to ensure that the `ShutdownWaiter` is dropped at the correct point
    ///
    /// This is identical to `drop(self)`.
    ///
    /// ## Usage
    ///
    /// ```
    /// let waiter = ShutdownWaiter::new().expect("the end is nigh");
    ///
    /// // do mission-critical stuff
    ///
    /// waiter.done();
    /// ```
    pub fn done(self) {}

    /// (*Internal*) Waits for all `ShutdownWaiter`s to be dropped, or for the timeout to expire
    ///
    /// This is allowed to be `async` because, at this stage in the shutdown, we still have the
    /// runtime available to us (just not in the usual fasion).
    ///
    /// This takes the receiver stored in the global executor. The returned value is true if the
    /// timeout expired.
    async fn wait(rx: oneshot::Receiver<()>, timeout: Duration) -> bool {
        tokio::time::timeout(timeout, rx).await.is_err()
    }
}

/// Spawns a set of tasks on the executor, only returning once all of the given futures have
/// finished.
///
/// The returned vector preserves the order of the original futures.
pub async fn run_all<F>(jobs: impl IntoIterator<Item = F>) -> Vec<F::Output>
where
    F: Future + Send + 'static,
    F::Output: Send + 'static,
{
    let handles = jobs.into_iter().map(spawn).collect::<Vec<_>>();
    let mut outputs = Vec::with_capacity(handles.len());
    for handle in handles {
        let res = match handle.await {
            Err(e) if e.is_panic() => std::panic::resume_unwind(e.into_panic()),
            res => res.expect("job never completed"),
        };

        outputs.push(res);
    }

    outputs
}

/// Blocks on the given future, running it to completion
///
/// This is only intended for use inside of `main`, and should not be used inside of synchronous
/// code anywhere else.
pub fn block_on<F: Future>(future: F) -> F::Output {
    require_initialized!(self);
    EXECUTOR.load().as_ref().unwrap().exec.block_on(future)
}

/// Starts a slow (normal) shutdown of the runtime
///
/// This cannot be called from within an `async` function; it shuts down the executor.
pub fn slow_shutdown() {
    require_initialized!(crate::runtime);

    // Currently, this is exactly the same as `unexpected_shutdown`. This might be changed at some
    // point in the future.
    // @def slow_shutdown v0

    // We take two steps here. First, we shut down the executor itself, followed by writing all
    // panic messages. Panics are kept for later in case shutdown causes any.

    // TODO-CORRECTNESS: This should probably loop if there's other references to the executor -
    // that could happen if people are spawning tasks *right now*.
    let exec = Arc::try_unwrap(EXECUTOR.swap(None).expect("runtime shutdown called twice"))
        .map_err(|_| "unexpected second executor reference")
        .unwrap();

    // Drop the stored sender so that we can wait on all `ShutdownWaiter`s to finish
    drop(exec.shutdown_tx);
    let did_timeout = exec
        .exec
        .block_on(ShutdownWaiter::wait(exec.shutdown_rx, SHUTDOWN_TIMEOUT));

    // TODO-ERROR: logging shouldn't be allowed to be async, even though it might be sped up. We
    // have no other way of reporting an error here if it timed out.
    // @req "log is async" v0
    if did_timeout {
        // TEMPORARY
        eprintln!("Warning: shutting down timed out!");
    }

    // See https://github.com/tokio-rs/tokio/pull/3174
    exec.exec.shutdown_timeout(Duration::from_nanos(1));

    panic::finalize();
}

/// Starts an immediate whole-program, unexpected shutdown
///
/// This is typically used in scenarios where we encountered some fatal error that we have no way
/// to report (e.g. an IO error from writing to `stdout`).
///
/// This cannot be called from within an `async` function; it shuts down the executor.
pub fn unexpected_shutdown() {
    // We currently use `slow_shutdown`. These should be split if there is ever a mismatch between
    // the spirit of this function and the behavior of `slow_shutdown`.
    // @req slow_shutdown v0
    log::error!("fatal error occured; performing unexpected shutdown");
    slow_shutdown();
}
