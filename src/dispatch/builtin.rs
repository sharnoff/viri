//! Support for the sorts of "builtin", intrinsic operations associated with extension dispatch

use std::collections::HashSet;
use std::fmt::Write;
use std::str::FromStr;

use super::*;
use crate::utils::DiscardResult;

/// A helper macro to define the various builtin operations in a centralized manner.
///
/// This produces a number of types and implementations, while also storing their type signatures.
/// The actual usage of these type signatures is inside the various methods called by
/// `handle_builtin`, but having them centralized is a huge benefit.
///
/// The only usage of this macro is immediately below; it should hopefully be fairly evident as to
/// what's going on.
macro_rules! ops {
    (
        $( #[$enum_attrs:meta] )*
        $vis:vis enum BuiltinOp {
            $( $(#[$attrs:meta])* $op:ident: type_sig![$arg_ty:ty => $res_ty:ty], )*
        }
    ) => {
        $( #[$enum_attrs] )*
        $vis enum BuiltinOp {
            $( $(#[$attrs])* $op, )*
        }

        impl FromStr for BuiltinOp {
            type Err = ();

            fn from_str(s: &str) -> Result<Self, ()> {
                match s {
                    $( stringify!($op) => Ok(Self::$op), )*
                    _ => Err(()),
                }
            }
        }

        /// Constructs the namespace of builtin operations and their "handlers"
        pub(super) fn initial_namespace() -> HashSet<String> {
            maplit::hashset! {
                $( stringify!($op).to_owned(), )*
            }
        }

        /// Helper macro for getting the argument type of a builtin operation
        ///
        /// This is provided so that changes to the type signatures here will produce compilation
        /// errors in casting elsewhere, instead of allowing those to be discovered through tests
        /// or at runtime.
        #[allow(unused_macros)]
        macro_rules! builtin_arg_ty {
            $(
            ($op) => { $arg_ty };
            )*
            ($unknown:ident) => { compile_error!("unknown builtin method"); }
        }

        /// Helper macro for getting the return type of a builtin operation
        ///
        /// This is provided so that changes to the type signatures here will produce compilation
        /// errors in casting elsewhere, instead of allowing those to be discovered through tests
        /// or at runtime.
        #[allow(unused_macros)]
        macro_rules! builtin_return_ty {
            $(
            ($op) => { $res_ty };
            )*
            ($method:ident) => { compile_error!("unknown builtin method"); };
        }
    }
}

ops! {
    #[derive(Copy, Clone)]
    pub enum BuiltinOp {
        /// Load the requested extension. This may return an error if the extension failed to load
        /// or does not exist.
        LoadExtension: type_sig![ExtensionPath => Result<ExtensionId, String>],

        /// Indicate that the sending extension has finished its loading process, regardless of
        /// whether that process was successful.
        ///
        /// Passing an error here indicates that it was a fatal error at extension startup; the
        /// extension will not receive any further requests.
        ///
        /// Returned errors can only result from improperly signalling that the extension was
        /// marked as finished twice.
        FinishedLoadingExtension: type_sig![Result<(), String> => Result<(), String>],

        /// Registers all of the provided strings as valid methods that can be called
        ///
        /// This can be called at any time, though is typically expected to be called while the
        /// extension is loading.
        Export: type_sig![Vec<String> => Result<(), String>],

        /// Un-registers a particular method, marking it as no longer available to be called
        ///
        /// Any events that were previously handled by this method will be ignored.
        UnExport: type_sig![String => Result<(), String>],

        /// Creates a new event, returning a unique UUID corresponding to the registered event
        ///
        /// This method can be used both for individual objects (e.g. text objects) *or* events
        /// that are global to a particular extension; it does not distinguish between them.
        RegisterEvent: type_sig![() => EventId],

        /// Unregisters the event given by the `EventId`. Returns an error if either: (a) the event
        /// does not exist, or (b) the event is not owned by the calling extension.
        UnregisterEvent: type_sig![EventId => Result<(), String>],

        RegisterHandler: type_sig![String => Result<(), String>],
        UnregisterHandler: type_sig![Name => bool],
    }
}

/// The result of attempting a "builtin" operation
///
/// We pass back a closure so that all error conditions can be checked initially without needing to
/// deal with the callback.
type BuiltinResult = Result<Box<dyn FnOnce(&mut BindingNamespace, Callback)>, String>;

impl BindingNamespace {
    /// Handles the builtin operation on the namespace, given the originating request
    pub(super) fn handle_builtin(
        &mut self,
        op: BuiltinOp,
        ext: ExtensionId,
        arg: Value,
        callback: Callback,
    ) {
        let res = match op {
            BuiltinOp::LoadExtension => self.load_extn(ext, arg),
            BuiltinOp::FinishedLoadingExtension => self.finish_load(ext, arg),

            BuiltinOp::Export => self.export(ext, arg),
            BuiltinOp::UnExport => self.un_export(ext, arg),

            BuiltinOp::RegisterEvent => self.register_event(ext, arg),
            BuiltinOp::UnregisterEvent => self.unregister_event(ext, arg),

            BuiltinOp::RegisterHandler => todo!(),
            BuiltinOp::UnregisterHandler => todo!(),
        };

        match res {
            Ok(func) => func(self, callback),
            Err(s) => {
                log::error!("{}", s);
                callback.send(Err(s)).discard_if_ok_else(|_| {
                    log::warn!("failed to send on callback: channel already closed");
                });
            }
        }
    }

    // Loads the given extension
    fn load_extn(&mut self, calling_ext: ExtensionId, path_val: Value) -> BuiltinResult {
        use ExtensionPath::{Builtin, Internal};

        let path: ExtensionPath = path_val
            .convert()
            .map_err(|e| format!("failed to convert extension path for loading: {}", e))?;

        if let ExtensionPath::Builtin = &path {
            return Err("erroneous request to load builtin extension".to_owned());
        }

        if let Some(&id) = self.ids.get(&path) {
            return Ok(Box::new(move |this, callback| {
                let this_paths = &this.paths;
                let paths = |id| this_paths.get(&id).unwrap();
                this.loader.load_existing(calling_ext, id, callback, paths);
            }));
        }

        match &path {
            Builtin => unreachable!(),
            Internal(ip_string) => {
                let ext = match crate::extensions::extension_handle(ip_string) {
                    Some(ext) => ext,
                    None => {
                        return Err(format!(
                            "attempted to load internal extension {:?}; none exists",
                            ip_string
                        ));
                    }
                };

                let new_id = ExtensionId::random();
                self.access.insert(new_id, ExtensionAccess::Internal(ext));
                self.ids.insert(path.clone(), new_id);
                self.paths.insert(new_id, path);

                crate::runtime::spawn(ext.load(self.builtin_id, new_id));

                Ok(Box::new(move |this, callback| {
                    let this_paths = &this.paths;
                    let paths = |id| this_paths.get(&id).unwrap();
                    this.loader.load_new(calling_ext, new_id, callback, paths);
                }))
            }
        }
    }

    // Wrapper around `LoadingHandler::finish_load` to handle value conversion and error handling
    fn finish_load(&mut self, calling_ext: ExtensionId, result: Value) -> BuiltinResult {
        let res: builtin_arg_ty![FinishedLoadingExtension] = result
            .convert()
            .map_err(|e| format!("failed to convert loading result: {}", e))?;

        // We received a message from the extension, so we *really* should at least know about it
        assert!(self.paths.contains_key(&calling_ext));

        Ok(Box::new(move |this, callback| {
            let this_paths = &this.paths;
            let paths = |id| this_paths.get(&id).unwrap();
            let finish_res = this.loader.finish_load(calling_ext, res, paths);

            // TODO: send `finish_res` inside `finish_load`, before checking for cycles.

            #[rustfmt::skip]
            callback.send(Ok(Some(
                Value::new(finish_res as builtin_return_ty![FinishedLoadingExtension])
            )))
                .discard_if_ok_else(|_| {
                    log::warn!("failed to send on 'finished loading' callback");
                });
        }))
    }

    fn export(&mut self, calling_ext: ExtensionId, arg: Value) -> BuiltinResult {
        let names: Vec<String> = arg
            .convert::<builtin_arg_ty![Export]>()
            .map_err(|e| e.to_string())?;

        Ok(Box::new(move |this, callback| {
            let methods = this
                .registry
                .get_mut(&calling_ext)
                .expect("no registry entry for extension");

            // We'll produce an error if any of the names are already present
            let duplicates: Vec<_> = names
                .iter()
                .filter_map(|n| if methods.contains(n) { Some(n) } else { None })
                .collect();

            if !duplicates.is_empty() {
                // We're putting a lot of work in here to produce a nice error message.
                //
                // Is this really necessary? Probably not - but it certainly looks nice. And that's
                // what counts.
                let msg = match duplicates.as_slice() {
                    [] => unreachable!(),
                    [single] => format!(
                        "cannot export name: {:?} is already registered for this extension",
                        single
                    ),
                    [pre @ .., last] => {
                        let mut arr = String::new();
                        for n in pre {
                            writeln!(arr, "{:?}, ", n).unwrap();
                        }
                        writeln!(arr, "{:?}", last).unwrap();

                        let quantifier = if pre.len() == 1 { "both" } else { "all" };
                        format!(
                            "cannot export names: [{}] {} already registered for this extension",
                            arr, quantifier
                        )
                    }
                };

                let result = Err(msg) as builtin_return_ty![Export];
                callback
                    .send(Ok(Some(Value::new(result))))
                    .discard_if_ok_else(|_| {
                        log::warn!("failed to send on callback: channel already closed")
                    });
                return;
            }

            // Done checking for duplicates.
            //
            // Now we can just add all of the names and return as such.
            methods.extend(names);
            let result: builtin_return_ty![Export] = Ok(());
            callback
                .send(Ok(Some(Value::new(result))))
                .discard_if_ok_else(|_| {
                    log::warn!("failed to send on 'finished loading' callback");
                });
        }))
    }

    fn un_export(&mut self, calling_ext: ExtensionId, arg: Value) -> BuiltinResult {
        let name: String = arg
            .convert::<builtin_arg_ty![UnExport]>()
            .map_err(|e| e.to_string())?;

        Ok(Box::new(move |this, callback| {
            let methods = this
                .registry
                .get_mut(&calling_ext)
                .expect("no registry for extension");

            let had_method = methods.remove(&name);
            let res: builtin_return_ty![UnExport] = match had_method {
                true => Ok(()),
                false => Err(format!(
                    "no method name {:?} to un-export for this extension",
                    name
                )),
            };

            callback
                .send(Ok(Some(Value::new(res))))
                .discard_if_ok_else(|_| {
                    log::warn!("failed to send on callback: channel already closed")
                });
        }))
    }

    fn register_event(&mut self, calling_ext: ExtensionId, unit_arg: Value) -> BuiltinResult {
        // We're expecting to receive nothing. We'll double-check that that's still the case
        let _: () = unit_arg
            .convert::<builtin_arg_ty![RegisterEvent]>()
            .map_err(|e| e.to_string())?;

        let id = EventId::random();
        self.owned_events
            .entry(calling_ext)
            .or_insert(HashSet::new())
            .insert(id);

        Ok(Box::new(move |_this, callback| {
            callback
                .send(Ok(Some(Value::new(id))))
                .discard_if_ok_else(|_| {
                    log::warn!("failed to send on callback: channel already closed")
                });
        }))
    }

    fn unregister_event(&mut self, calling_ext: ExtensionId, ext_id: Value) -> BuiltinResult {
        let event_id: EventId = ext_id
            .convert::<builtin_arg_ty![UnregisterEvent]>()
            .map_err(|e| e.to_string())?;

        // Events are referenced in three fields in a `BindingNamespace`:
        // * `handlers`,
        // * `owned_events`, and
        // * `owned_handlers`.
        //
        // Remove this event from its owner, if the calling extension *does* actually own it.
        let this_ext_owned = self
            .owned_events
            .get_mut(&calling_ext)
            .map(|set| set.remove(&event_id))
            .unwrap_or(false);

        let mut exists = false;
        // Only remove the event if it's actually owned by the caller
        if this_ext_owned {
            // Remove the event from `handlers`.
            let handlers = self.handlers.remove(&event_id);
            exists = handlers.is_some();

            // Remove all references to the event from `owned_handlers`. This *could* be made more
            // efficient in the case where there's many extensions, but that probably doesn't
            // matter too much.
            //
            // There *is* some unnecessary cloning and bad access patterns here, so that's
            // something that we could improve at some point. (TODO-PERF)
            for name in handlers.into_iter().flatten() {
                let set = self
                    .owned_handlers
                    .get_mut(&name.extension_id)
                    .expect("handler for extension that does not exist");

                set.remove(&(event_id, name.method.clone()));
            }
        }

        Ok(Box::new(move |_, callback| {
            let res: builtin_return_ty![UnregisterEvent] = if exists && !this_ext_owned {
                Err("cannot unregister event: not owned by this extension".into())
            } else if !exists {
                Err("cannot unregister event: event does not exist".into())
            } else {
                Ok(())
            };

            callback
                .send(Ok(Some(Value::new(res))))
                .discard_if_ok_else(|_| {
                    log::warn!("failed to send on callback: channel already closed")
                });
        }))
    }
}
