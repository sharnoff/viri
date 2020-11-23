//! Components of the low-level functioning of the editor

use crate::macros::{init, require_initialized};
use lazy_static::lazy_static;
use std::future::Future;
use tokio::runtime::{Builder as ExecutorBuilder, Runtime as TokioExecutor};
use tokio::task::JoinHandle;

mod panic;

lazy_static! {
    // The async executor
    //
    // This is never exposed directly, but can be accessed through the `spawn`
    static ref EXECUTOR: TokioExecutor = {
        // We explicitly build the executor so that we can ensure it's multithreaded
        ExecutorBuilder::new_multi_thread()
            .thread_name("viri-rt-worker")
            .build()
            .expect("failed to build the core executor")
    };
}

// @def runtime::init v0
init! {
    // There isn't much runtime initialization to do, other than to ensure that the executor has
    // been built before we use it
    lazy_static::initialize(&EXECUTOR);

    mod panic;
}

/// Spawns a single task on the executor, returning a `JoinHandle` for the task
///
/// The join handle can be safely dropped and the executor will continue attempting to complete it.
pub fn spawn<F>(future: F) -> JoinHandle<F::Output>
where
    F: Future + Send + 'static,
    F::Output: Send + 'static,
{
    require_initialized!(crate::runtime);
    EXECUTOR.spawn(future)
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
    EXECUTOR.block_on(future)
}

/// Starts a slow (normal) shutdown of the runtime
pub fn slow_shutdown() {
    // TODO-CORRECTNESS - clear the rest of the runtime stuff?
    panic::finalize();
}

/// Starts an immediate whole-program, unexpected shutdown
///
/// This is typically used in scenarios where we encountered some fatal error that we have no way
/// to report (e.g. an IO error from writing to `stdout`).
pub fn unexpected_shutdown() {
    log::error!("fatal error occured; performing unexpected shutdown");
    todo!()
}
