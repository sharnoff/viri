//! Support for the sorts of "builtin", intrinsic operations associated with extension dispatch

use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display, Formatter};
use std::str::FromStr;

use super::*;
use crate::macros::type_sig;
use crate::utils::DiscardResult;

/// The extension name used to refer to the built-in operations
pub static BUILTIN_NAME: &str = "builtin";

/// The various intrinsic operation supported to allow the manipulation of bindings and extensions
#[derive(Copy, Clone)]
pub enum BuiltinOp {
    /// Load the requested extension
    LoadExtension,
    /// Indicate that the sending extension has finished its loading process. Type `() -> ()`.
    FinishedLoadingExtension,
    SetAlias,
    RegisterHandler,
    ReplaceHandler,
    UnregisterHandler,
}

impl FromStr for BuiltinOp {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, ()> {
        match s {
            "LoadExtension" => Ok(Self::LoadExtension),
            "FinishedLoadingExtension" => Ok(Self::FinishedLoadingExtension),
            "SetAlias" => Ok(Self::SetAlias),
            "RegisterHandler" => Ok(Self::RegisterHandler),
            "ReplaceHandler" => Ok(Self::ReplaceHandler),
            "UnregisterHandler" => Ok(Self::UnregisterHandler),
            _ => Err(()),
        }
    }
}

/// Constructs the namespace of builtin operations and their "handlers"
pub(super) fn initial_namespace() -> HashMap<String, Signature> {
    // Helper macro for defining this namespace
    macro_rules! bn {
        ( [$ext_id:expr]; $($key:ident => $type_sig:expr,)* ) => {{
            maplit::hashmap! {
                $( stringify!($key).to_owned() => $type_sig, )*
            }
        }}
    }

    bn! {
        [builtin_id];
        LoadExtension => type_sig![ExtensionPath -> ExtensionId],
        FinishedLoadingExtension => type_sig![() -> ()],
        SetAlias => type_sig![String -> ()],
        RegisterHandler => type_sig![{ name: Name, allow_replaced: bool } -> bool],
        ReplaceHandler => type_sig![Name -> ()],
        UnregisterHandler => type_sig![Name -> bool],
    }
}

impl BindingNamespace {
    /// Handles the builtin operation on the namespace, given the originating request
    pub(super) fn handle_builtin(
        &mut self,
        op: BuiltinOp,
        arg: Value<'static>,
        callback: Callback,
    ) {
        match op {
            BuiltinOp::LoadExtension => self.load_extn(arg.convert(), callback),
            BuiltinOp::FinishedLoadingExtension => todo!(),
            BuiltinOp::SetAlias => todo!(),
            BuiltinOp::RegisterHandler => todo!(),
            BuiltinOp::ReplaceHandler => todo!(),
            BuiltinOp::UnregisterHandler => todo!(),
        }
    }

    fn load_extn(&mut self, path: ExtensionPath, callback: Callback) {
        use ExtensionPath::{Builtin, Internal};

        match path {
            Builtin => {
                log::error!("erroneous request to load builtin extension");
                callback
                    .send(Err("erroneous request to load builtin extension".to_owned()))
                    .discard_if_ok_else(|_| {
                        log::warn!("failed to send on callback: channel already closed");
                    });
            }
            Internal(ip_string) => {
                let ext = match crate::extensions::extension_handle(&ip_string) {
                    Some(ext) => ext,
                    None => {
                        log::error!(
                            "attempted to load internal extension {:?}; none exists",
                            ip_string
                        );
                        callback
                            .send(Err(format!(
                                "cannot load internal extension {:?}; none exists",
                                ip_string,
                            )))
                            .discard_if_ok_else(|_| {
                                log::warn!("failed to send on callback: channel already closed");
                            });
                        return;
                    }
                };

                // We need to provide a channel, even though it's never used; dropping the receiver
                // means that sending will produce an error, but that's fine.
                let finish_req = Request {
                    originating_ext: self.builtin_id,
                    kind: RequestKind::GetValue {
                        from: Name {
                            extension_id: self.builtin_id,
                            method: "FinishedLoadingExtension".to_owned(),
                        },
                        arg: Value::new(()),
                    },
                };

                // The UUID assigned to this extension
                let ext_id = ExtensionId(Uuid::new_v4());
                self.ids.insert(Internal(ip_string), ext_id);

                // TODO: add this extension to a holding set of extensions that are *currently*
                // loading, but we're waiting on them to finish. The callback needs to go there in
                // case we need to send back an error as a result of a cycle.

                let builtin_id = self.builtin_id;
                crate::runtime::spawn(async move {
                    // Actually do the loading
                    ext.load(builtin_id, ext_id).await;
                    // Once it's loaded, register it as such
                    let _ = finish_req.spawn().await;
                });
            }
        }
    }
}

/// A handler responsible for coordinating the loading of extensions
pub(super) struct LoadingHandler {
    // The set of extensions that are still loading, with their callbacks and all of the extensions
    // that they are blocked on
    loading: HashMap<ExtensionId, (Callback, HashSet<ExtensionId>)>,

    // The set of extensions that have not yet blocked on loading something
    free_set: HashSet<ExtensionId>,

    // Typically the ID of the builtin extension -- it serves as an initial seed
    base: ExtensionId,

    // True if a loading cycle has occured
    poisoned: bool,
}

pub(super) struct LoadCycleError(Vec<ExtensionId>);

impl LoadingHandler {
    /// Constructs a new `LoadingHandler`, given the initial seed extension. The initial seed is
    /// typically just the ID of the "builtin" extension
    pub fn new(seed: ExtensionId) -> Self {
        LoadingHandler {
            loading: HashMap::new(),
            free_set: HashSet::new(),
            base: seed,
            poisoned: false,
        }
    }

    /// Registers an extension as being required by another to load
    ///
    /// If an extension that has already finished loading must load another, the correct `source`
    /// is the builtin extension (i.e. the `base`, or `seed` provided to `Self::new`)
    pub fn add_required_load(
        &mut self,
        source: ExtensionId,
        to_load: ExtensionId,
    ) -> Result<(), LoadCycleError> {
        if self.poisoned {
            return Ok(());
        }

        assert!(source == self.base || self.loading.contains_key(&source));

        // Add `to_load` as a requirement for `source`
        if let Some((_, set)) = self.loading.get_mut(&source) {
            set.insert(to_load);
        }

        self.free_set.remove(&to_load);

        if self.free_set.is_empty() {
            self.poisoned = true;
            let cycle = self.find_load_cycle();
            self.report_cycle(&cycle);
            return Err(cycle);
        }

        Ok(())
    }

    /// Records that the given extension has finished loading, and therefore cannot be included in
    /// any cycles
    ///
    /// Any error returned will have already been handled.
    pub fn finish_load(&mut self, ext: ExtensionId) -> Result<(), Option<LoadCycleError>> {
        if self.poisoned {
            return Ok(());
        }

        let previous = self.loading.remove(&ext);

        if self.free_set.is_empty() && !self.loading.is_empty() {
            let cycle = Some(self.find_load_cycle());
        }

        match self.loading.remove(&ext) {
            Some(_) if self.free_set.is_empty() && !self.loading.is_empty() => {
                self.poisoned = true;
                let cycle = self.find_load_cycle();
                self.report_cycle(&cycle);
                Err(Some(cycle))
            }
            Some(_) => Ok(()),
            None => Err(None),
        }
    }

    /// Finds a single cycle in the graph of loading dependencies, assuming that one exists
    ///
    /// This method panics if there is no cycle.
    fn find_load_cycle(&self) -> LoadCycleError {
        use std::collections::{hash_map::Entry, hash_set};

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

        // From each `id` in `self.loading`, we'll try to find a cycle.
        for (&id, set) in self.loading.iter().map(|(id, (_, set))| (id, set)) {
            match marks.entry(id) {
                // If there's already an entry in `marks`, it must be "explored"; there's no sense
                // in repeating work
                Entry::Occupied(_) => continue,
                // Otherwise, we'll set it as "partial", because it's now in progress as the root
                // of this search
                Entry::Vacant(v) => drop(v.insert(Label::Partial)),
            }

            let mut stack = vec![StackElem {
                id,
                edges: self.loading[&id].1.iter(),
            }];

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
                            edges: self.loading[&next_id].1.iter(),
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
    fn report_cycle(&mut self, cycle: &LoadCycleError) {
        for id in &cycle.0 {
            let prev = self.loading.remove(id).expect("");
            prev.0
                .send(Err(
                    "cannot load load dependencies; they form a cycle".to_owned()
                ))
                .discard_result();
        }
    }
}

impl LoadCycleError {
    fn display_with_paths<'a>(
        &'a self,
        paths: impl 'a + Fn(ExtensionId) -> &'a ExtensionPath,
    ) -> impl 'a + Display {
        struct Disp<'a, F> {
            ids: &'a [ExtensionId],
            paths: F,
        }

        impl<'a, F: Fn(ExtensionId) -> &'a ExtensionPath> Display for Disp<'a, F> {
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
