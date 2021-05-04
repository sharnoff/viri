//! Utilities for coordinating external extension loading
//!
//! There's a few notable items exported from this module. The primary export is
//! [`LoadingHandler`], which serves to track the dependency graph of extensions and detect cycles
//! if/when they occur.

use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display, Formatter};
use std::mem;

use super::{Callback, ExtensionId, ExtensionPath, Value};
use crate::utils::DiscardResult;

/// A handler responsible for coordinating the loading of extensions
///
/// Cycles are only detected once all currently-loading extensions have the potential to be blocked
/// on each other. We say "the *potential* to be blocked" because it's possible for extensions to
/// continue working while waiting for another one to load, but we know that - if loading other
/// extensions is a requirement for it to load - it'll never finish if there's circular
/// dependencies.
pub(super) struct LoadingHandler {
    // The set of extensions that are still loading, with their callbacks for each attempted load
    // that they're still blocked on
    loading: HashMap<ExtensionId, LoadingInfo>,

    // The set of extensions that are not currently loading anything. We'll assume that if an
    // extension is attempting to load something, it's *some kind* of blocked. This turns out to be
    // a fine assumption, because - even if it isn't really blocked *yet*, it'll still ask for that
    // extension to be loaded.
    free_set: HashSet<ExtensionId>,

    // Typically the ID of the builtin extension -- it serves as an initial seed
    base: ExtensionId,
}

/// Information about the loading of a particular extension
struct LoadingInfo {
    // The extensions currently blocked on this one
    waiting: HashMap<ExtensionId, Callback>,

    // All of the extensions that this extension is currently blocked on, with the callbacks to
    // send the end result on
    blocked_on: HashSet<ExtensionId>,

    // It's possible that this extension couldn't be loaded - either because of its own internal
    // error or a dependency cycle. IF so, this contains an error message that can be given to
    // indicate as such.
    failed_with: Option<String>,
}

impl LoadingInfo {
    /// Helper function for constructing a new `LoadingInfo` as blocked on waiting for another
    /// extension to load
    fn new_blocked(to_load: ExtensionId) -> Self {
        LoadingInfo {
            waiting: HashMap::new(),
            blocked_on: maplit::hashset!(to_load),
            failed_with: None,
        }
    }

    /// Helper function for constructing a new `LoadingInfo` with a single extension waiting
    fn new_waiting(waiting: ExtensionId, callback: Callback) -> Self {
        LoadingInfo {
            waiting: maplit::hashmap!(waiting => callback),
            blocked_on: HashSet::new(),
            failed_with: None,
        }
    }
}

/// An error resulting from a circular extension loading dependency
///
/// The values are ordered so that the extension from index `i` depends on the one from index
/// `(i + 1) % n`.
pub(super) struct LoadCycleError(Vec<ExtensionId>);

impl LoadingHandler {
    /// Constructs a new `LoadingHandler`, given the initial seed extension. The initial seed is
    /// typically just the ID of the "builtin" extension
    pub fn new(seed: ExtensionId) -> Self {
        LoadingHandler {
            loading: HashMap::new(),
            free_set: HashSet::new(),
            base: seed,
        }
    }

    /// Waits for the given extension to finish loading
    ///
    /// This method is somewhat complicated -- read this part carefully. The extension to load must
    /// *already* exist. If we find that we don't have any information about it, we'll assume that
    /// it was successfully loaded. In this case, we'll immediately send a success value on the
    /// callback.
    ///
    /// Extensions that fail to load -- either due to a internal errors or cycles -- will be
    /// quietly ignored unless they indicate otherwise.
    pub fn load_existing<'a>(
        &mut self,
        source: ExtensionId,
        to_load: ExtensionId,
        callback: Callback,
        paths: impl 'a + Fn(ExtensionId) -> &'a ExtensionPath,
    ) {
        // Even though we already have access to the `ExtensionId` assigned to the extension that
        // we're supposed to be loading, the definition of the API means that we only return when
        // the extension has *finished* loading -- we can't send it yet

        let load_info = match self.loading.get_mut(&to_load) {
            None => {
                // doc comment above explains that no entry means it's finished
                #[rustfmt::skip]
                callback.send(Ok(Some(
                    Value::new(Ok(to_load) as builtin_return_ty![LoadExtension])
                )))
                    .discard_if_ok_else(|_| log::warn!("failed to send on loading callback"));
                return;
            }
            Some(info) => info,
        };

        // If this extension already failed to load, we can just send that along to the callback
        // immediately.
        if let Some(err_msg) = load_info.failed_with.as_ref() {
            #[rustfmt::skip]
            callback.send(Ok(Some(
                Value::new(Err(err_msg.clone()) as builtin_return_ty![LoadExtension])
            )))
                .discard_if_ok_else(|_| log::warn!("failed to send on loading callback"));
            return;
        }

        load_info.waiting.insert(source, callback);

        // If `source` is currently loading as well, mark it as blocked on `to_load`:
        if let Some(e) = self.loading.get_mut(&source) {
            e.blocked_on.insert(to_load);
            // If the extension that requested this wasn't blocked on anything before, it is now.
            self.free_set.remove(&source);
        }

        // If all of the extensions we know about are waiting for others to finish loading, then we
        // must have a cycle somewhere. We'll find that and report it.
        while self.free_set.is_empty() && !self.loading.is_empty() {
            let cycle = self.find_load_cycle();
            self.report_cycle(&cycle, &paths);
        }
    }

    /// Registers a new extension that needs to be loaded
    pub fn load_new<'a>(
        &mut self,
        source: ExtensionId,
        to_load: ExtensionId,
        callback: Callback,
        paths: impl 'a + Fn(ExtensionId) -> &'a ExtensionPath,
    ) {
        self.loading
            .insert(to_load, LoadingInfo::new_waiting(source, callback));

        if let Some(e) = self.loading.get_mut(&source) {
            e.blocked_on.insert(to_load);
            self.free_set.remove(&source);
        }

        // We don't need to check if there's a cycle here; we can't have one because this new
        // extension isn't blocked yet.
    }

    /// Records that the given extension has finished loading, and therefore cannot be included in
    /// any cycles
    ///
    /// The provided result is passed to all other extensions that were waiting for this to load.
    ///
    /// It is possible for this method to "discover" that there are loading cycles; if this
    /// happens, those will be silently reported.
    ///
    /// ## Errors
    ///
    /// This method will return an error if the provided extension either (a) has not started
    /// loading, or (b) has already finished.
    pub fn finish_load<'a>(
        &mut self,
        ext: ExtensionId,
        result: Result<(), String>,
        paths: impl 'a + Fn(ExtensionId) -> &'a ExtensionPath,
    ) -> Result<(), String> {
        let waiting;

        match self.loading.entry(ext) {
            // The extension passed in already exists, so we know that it must have been loading at
            // *some point*. If it isn't loading any more, that's an error.
            Entry::Vacant(_) => return Err("extension has already finished loading".into()),

            // Only remove the existing extension if the loading failed for some reason
            Entry::Occupied(mut entry) => match result.as_ref() {
                Err(msg) => {
                    let e = entry.get_mut();
                    waiting = mem::replace(&mut e.waiting, HashMap::new());
                    e.failed_with = Some(msg.clone());
                    e.blocked_on = HashSet::new();
                }
                Ok(()) => {
                    let e = entry.remove();
                    waiting = e.waiting;
                }
            },
        }

        for (id, callback) in waiting {
            #[rustfmt::skip]
            callback.send(Ok(Some(
                Value::new(result.clone() as builtin_return_ty![FinishedLoadingExtension])
            )))
                .discard_if_ok_else(|_| {
                    log::warn!("failed to send on loading callback");
                });

            if let Some(e) = self.loading.get_mut(&id) {
                e.blocked_on.remove(&ext);
                if e.blocked_on.is_empty() {
                    self.free_set.insert(id);
                }
            }
        }

        while self.free_set.is_empty() && !self.loading.is_empty() {
            let cycle = self.find_load_cycle();
            self.report_cycle(&cycle, &paths);
        }

        Ok(())
    }

    /// Finds a single cycle in the graph of loading dependencies, assuming that one exists
    ///
    /// This method panics if there is no cycle.
    fn find_load_cycle(&self) -> LoadCycleError {
        use std::collections::hash_set;

        // To find a cycle, we can just use a standard depth-first search

        // The label on a particular "node". Anything that's "partial" will be present in the
        // stack, and anything that's "explored" has already been found to not lead to a cycle.
        enum Label {
            Partial,
            Explored,
        }

        struct StackElem<'a> {
            edges: hash_set::Iter<'a, ExtensionId>,
            id: ExtensionId,
        }

        let mut marks = <HashMap<ExtensionId, Label>>::new();

        // Helper function to produce the stack elements for an ExtensionId
        #[rustfmt::skip]
        let stack_elem = |id| StackElem { id, edges: self.loading[&id].blocked_on.iter() };

        // From each `base_id` in `self.loading`, we'll try to find a cycle.
        for base_id in self.loading.iter().map(|(id, _)| *id) {
            match marks.entry(base_id) {
                // If there's already an entry in `marks`, it must have been "explored"; there's no
                // sense in repeating work
                Entry::Occupied(_) => continue,
                // Otherwise, we'll set it as "partial", because it's now in progress as the root
                // of this search
                Entry::Vacant(v) => drop(v.insert(Label::Partial)),
            }

            let mut stack = vec![stack_elem(base_id)];

            // Loop until the stack is empty
            'stack_is_empty: loop {
                // Get the next id to explore off the top of the stack
                let next_id = loop {
                    let last = match stack.last_mut() {
                        Some(l) => l,
                        None => break 'stack_is_empty,
                    };

                    // Get the next id from the last thing on the stack. If it doesn't have
                    // anything left, remove it from the stack so we can move on to the next one.
                    match last.edges.next().cloned() {
                        Some(id) => break id,
                        None => {
                            // As we're removing it from the stack, we know that it doesn't lead to
                            // a cycle, so we should mark it as such.
                            marks.insert(last.id, Label::Explored);
                            stack.pop();
                        }
                    }
                };

                match marks.entry(next_id) {
                    // The node hasn't been seen before; we'll mark it as now being in progress,
                    // before adding it to the stack
                    Entry::Vacant(v) => {
                        v.insert(Label::Partial);
                        stack.push(StackElem {
                            id: next_id,
                            edges: self.loading[&next_id].blocked_on.iter(),
                        });
                    }

                    // If it's already been fully explored, there's no need to look at it again.
                    // We'll just continue on to the next edge at the top of the stack
                    Entry::Occupied(o) if matches!(o.get(), Label::Explored) => continue,

                    // If it's not `Explored`, it must be `Partial`; we have a cycle, with the
                    // elements given by the stack.
                    Entry::Occupied(_) => {
                        // Get the index in the stack that the cycle starts at
                        let cycle_start = stack
                            .iter()
                            .enumerate()
                            .rev()
                            .find(|(_, elem)| elem.id == next_id)
                            .map(|(i, _)| i)
                            .expect(
                                "found partial entry without corresponding id earlier in stack",
                            );

                        let cycle = stack[cycle_start..].iter().map(|elem| elem.id).collect();
                        return LoadCycleError(cycle);
                    }
                }
            }
        }

        // If we get to this point and we still haven't found a cycle, there was some kind of
        // error. We'll panic to indicate this.
        panic!("`find_load_cycle` couldn't find a cycle")
    }

    /// Sends an error on all callback channels reported as part of the cycle
    fn report_cycle<'a, 'b: 'a>(
        &mut self,
        cycle: &LoadCycleError,
        paths: impl 'a + Fn(ExtensionId) -> &'b ExtensionPath,
    ) {
        // We'll go through this in a few phases. In the first phase, we'll handle all of the
        // responses to each member of the cycle in turn. We'll then clean up anything else that
        // was waiting for these to finish.

        // Pairs of each cycle[i] with cycle[(i + 1) % n]
        let pairs = cycle.0.iter().zip(cycle.0.iter().cycle().skip(1));

        let cycle_msg = format!(
            "cannot load extension; dependencies form a cycle:\n{}",
            cycle.display_with_paths(&paths)
        );
        let cycle_res = Err(cycle_msg) as builtin_return_ty![LoadExtension];

        for (id, dep) in pairs {
            let dep_info = self.loading.get_mut(dep).unwrap();
            let callback = dep_info.waiting.remove(id).unwrap();
            callback
                .send(Ok(Some(Value::new(cycle_res.clone()))))
                .discard_if_ok_else(|_| {
                    log::warn!("failed to report extension load cycle on loading callback")
                });

            // While we're sending the cycle error to each of the callbacks, we also need to remove
            // the corresponding back edges in the graph.
            let id_info = self.loading.get_mut(id).unwrap();
            id_info.blocked_on.remove(dep);

            if id_info.blocked_on.is_empty() {
                self.free_set.insert(*id);
            }
        }

        // While we could wait for the extensions to error out and indicate they've finished, it's
        // better for us to just preemptively do that. We might otherwise have multiple (possibly
        // many!) cycles reported, and that's not exactly helpful.

        for id in &cycle.0 {
            let info = self.loading.get_mut(id).unwrap();

            // We use a different message to send to anything that was previously waiting on this
            // extension to load that *wasn't* part of the cycle; the full cycle isn't relevant to
            // them.
            let failure_msg = format!("dependencies of extension {} form a cycle", paths(*id));
            info.failed_with = Some(failure_msg.clone());

            // All of the extensions that were waiting on this one to load should be given an
            // appropriate error. We need to remove the connection from both sides -- hence why we
            // clear `info.waiting`
            let waiting = mem::replace(&mut info.waiting, HashMap::new());
            let secondary_error = Ok(Some(Value::new(
                Err(failure_msg) as builtin_return_ty![LoadExtension]
            )));

            for (w_id, callback) in waiting {
                callback
                    .send(secondary_error.clone())
                    .discard_if_ok_else(|_| {
                        log::warn!("failed to send extension loading error on callback")
                    });

                let w_info = self.loading.get_mut(&w_id).unwrap();
                w_info.blocked_on.remove(id);
            }
        }
    }
}

impl LoadCycleError {
    /// Returns a private type that allows pretty formatting of the error
    ///
    /// Typical errors may produce a displayed message like:
    /// ```text
    /// ┌─────┐
    /// │   file <internal>
    /// │     ↓
    /// │   text <internal>
    /// │     ↓
    /// │   cursor <internal>
    /// └─────┘
    /// ```
    /// (This example is a little contrived; try to look past that for now.)
    fn display_with_paths<'a, 'b: 'a>(
        &'a self,
        paths: impl 'a + Fn(ExtensionId) -> &'b ExtensionPath,
    ) -> impl 'a + Display {
        struct Disp<'a, F> {
            ids: &'a [ExtensionId],
            paths: F,
        }

        impl<'a, 'b, F: Fn(ExtensionId) -> &'b ExtensionPath> Display for Disp<'a, F> {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                writeln!(f, "┌─────┐")?;

                for (i, path) in self.ids.iter().cloned().map(&self.paths).enumerate() {
                    if i != 0 {
                        writeln!(f, "│     ↓")?;
                    }
                    writeln!(f, "│   {}", path)?;
                }

                writeln!(f, "└─────┘")
            }
        }

        Disp {
            ids: &self.0,
            paths,
        }
    }
}
