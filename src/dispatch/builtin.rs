//! Support for the sorts of "builtin", intrinsic operations associated with extension dispatch

use std::collections::HashMap;
use std::str::FromStr;

use super::*;
use crate::macros::type_sig;
use crate::utils::DiscardResult;

/// The extension name used to refer to the built-in operations
pub static BUILTIN_NAME: &str = "builtin";

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
        pub(super) fn initial_namespace() -> HashMap<String, Signature> {
            maplit::hashmap! {
                $( stringify!($op).to_owned() => type_sig![$arg_ty => $res_ty], )*
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

        SetAlias: type_sig![String => ()],
        // RegisterHandler: type_sig![{ name: Name, allow_replaced: bool } => bool],
        ReplaceHandler: type_sig![Name => ()],
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
            BuiltinOp::FinishedLoadingExtension => todo!(),
            BuiltinOp::SetAlias => todo!(),
            // BuiltinOp::RegisterHandler => todo!(),
            BuiltinOp::ReplaceHandler => todo!(),
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
}
