//! The runtime parameters available for use and update at any point
//!
//! Parameters are represented by a hashmap strings to values that might not be present. These must
//! be registered before use with [`register_rt_param`] before they can be accessed. This is
//! typically done at program initialization. Additionally, validator functions can be given for
//! each parameter in order to prevent bad values being assigned, with [`set_rt_param_validator`].
//!
//! There's also the `require_param` macro defined in this module - we can't generate documentation
//! for this, but it is defined within this module, towards the bottom.
//!
//! These are primarily modified by the `set` command in colon mode.
//!
//! [`register_rt_param`]: fn.register_rt_param.html
//! [`set_rt_param_validator`]: fn.set_rt_param_validator.html

use crate::utils::OpaqueOption;
use lazy_static::lazy_static;
use std::collections::HashMap;
use std::fmt::{self, Debug, Formatter};
use std::sync::atomic::{AtomicBool, Ordering::SeqCst};
use std::sync::Mutex;

lazy_static! {
    /// The runtime parameters provided by the `set` colon command
    ///
    /// This is exposed internally through the [`set_runtime_value`] function, and simply provides
    /// a map of string keys (e.g. `color_line_numbers`) to values (e.g. `yes` or `yellow`).
    ///
    /// All runtime parameters *must* have an entry here. For more information, see
    /// [`RTParamInfo`].
    ///
    /// [`set_runtime_value`]: fn.set_runtime_value.html
    /// [`RTParamInfo`]: struct.RTParamInfo.html
    static ref RUNTIME_PARAMS: Mutex<HashMap<&'static str, RTParamInfo>> = Mutex::new(HashMap::new());
}

/// A marker to track whether any runtime values have been updated
///
/// This is used by the container instance to force redrawing of all views whenever there's been a
/// change in any runtime parameters.
pub(super) static CHANGED_RUNTIME_VALS: AtomicBool = AtomicBool::new(false);

/// Information for any particular runtime parameter
///
/// Every parameter in use will have a corresponding entry to indicate that it *is* indeed in use.
/// Note that this does not include the actual name of the parameter; this is given by the key in
/// the containing map.
#[derive(Clone, Default)]
struct RTParamInfo {
    /// The value of the runtime parameter, if it has been set
    value: Option<String>,

    /// A validator function for determining whether the assigned value is valid.
    ///
    /// This value need not be present, in which case this instance might only serve to indicate
    /// that the parameter exists.
    is_valid: Option<fn(&str) -> Result<(), String>>,
}

/// Sets a runtime parameter, returning an error if it is unknown or invalid
///
/// Retrieving these values can be done via the [`get_runtime_param`] function.
///
/// Runtime parameters are global to the entire application, and so a successful assignment here
/// will cause a full refresh of all views.
///
/// Errors may be returned under two cases: (1) if the key is unknown - i.e. if it has not been
/// marked as used by [`register_rt_param`] - or (2) if the value is invalid, as given by a
/// validator function provided by [`set_rt_param_validator`].
///
/// [`get_rt_param`]: fn.get_rt_param.html
/// [`register_rt_param`]: fn.requires_rt_param.html
/// [`set_rt_param_validator`]: fn.set_rt_param_validator.html
pub fn set_runtime_param(param: &str, val: String) -> Result<(), String> {
    let mut guard = RUNTIME_PARAMS.lock().unwrap();

    let mut entry = match guard.get_mut(param) {
        None => return Err(format!("Unknown runtime parameter '{}'", param)),
        Some(e) => e,
    };

    // If there's a validator, we'll check that the value is okay
    if let Some(validator) = entry.is_valid.as_ref() {
        validator(&val)?;
    }

    entry.value = Some(val);
    CHANGED_RUNTIME_VALS.store(true, SeqCst);
    Ok(())
}

/// Gets the value of the given runtime parameter, returning `None` if it has not been set
///
/// This requires that the parameter already be registered by [`register_rt_param`]; this function
/// will panic if this is not the case. Additionally, if a validator function has been set by
/// [`set_rt_param_validator`], any returned value will be guaranteed to satisfy the validator.
///
/// [`register_rt_param`]: fn.register_rt_param.html
/// [`set_rt_param_validator`]: fn.set_rt_param_validator.html
pub fn get_runtime_param(param: &str) -> Option<String> {
    let guard = RUNTIME_PARAMS.lock().unwrap();

    match guard.get(param) {
        None => {
            // Because this error is likely to happen at runtime, we intentionally don't drop the
            // guard, because we'd rather poison it and cause whole-program shutdown.
            panic!(concat!(
                "fatal internal error: attempted to get value of unregistered runtime param\n",
                "help: use `container::register_rt_param` to make this parameter known",
            ));
        }
        Some(entry) => entry.value.clone(),
    }
}

/// Registers the runtime parameter as used in some form
///
/// This *must* be called for each parameter that may be used during runtime; if it is not,
/// attempting to retrieve the value will panic.
///
/// This function (unlike [`set_rt_param_validator`]) may be called multiple times for the same
/// parameter name.
pub fn register_rt_param(param: &'static str) {
    let mut guard = RUNTIME_PARAMS.lock().unwrap();

    if !guard.contains_key(param) {
        guard.insert(param, RTParamInfo::default());
    }
}

/// Sets the validation function for a runtime parameter
///
/// This may be used to prevent bad values being given for certain parameters, for example ensuring
/// that tabstops must be a positive integer. The given function should return an error message to
/// give to the user.
///
/// ## Semantics
///
/// The validator for the same parameter must not be set multiple times; if this is attempted, this
/// function will panic. Additionally, [`register_rt_param`] must be called for the parameter
/// before this function.
///
/// If a validator is added to a parameter after its value is set to something marked as invalid,
/// then a warning will be emitted and the original value returned. This is given by the first
/// value in the error variant of the return. The second element in the tuple gives the resulting
/// error message from the validator.
pub fn set_rt_param_validator(
    param: &str,
    is_valid: fn(&str) -> Result<(), String>,
) -> Result<(), (String, String)> {
    let mut guard = RUNTIME_PARAMS.lock().unwrap();

    match guard.get_mut(param) {
        None => panic!(concat!(
            "fatal internal error: attempted to set validator of unregistered runtime param\n",
            "help: use `container::register_rt_param` to make this parameter known",
        )),
        Some(entry) if entry.is_valid.is_some() => panic!(
            "fatal internal error: attempted to twice set validator of runtime param '{}'",
            param
        ),
        Some(mut entry) => {
            entry.is_valid = Some(is_valid);
            match entry.value.as_ref().map(|v| (v, is_valid(&v))) {
                None | Some((_, Ok(_))) => Ok(()),
                Some((v, Err(msg))) => {
                    log::warn!(
                        "warning: discarding value for runtime parameter `{}` as new validator fails with: {}",
                        param,
                        msg,
                    );
                    let res = Err((v.clone(), msg));
                    entry.value = None;
                    res
                }
            }
        }
    }
}

macro_rules! require_param {
    ($($param:expr $(=> $is_valid:expr)?),*$(,)?) => {{
        $(
            $crate::container::params::register_rt_param($param);
            // TODO: It might be better to not unwrap here, and instead
            $($crate::container::params::set_rt_param_validator($param, $is_valid).unwrap();)?
        )*
    }}
}

////////////////////////////////////////////////////////////////////////////////
// Boilerplate implementations                                                //
////////////////////////////////////////////////////////////////////////////////

impl Debug for RTParamInfo {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        fmt.debug_struct("RTParamInfo")
            .field("value", &self.value)
            .field("is_valid", &OpaqueOption::from(&self.is_valid))
            .finish()
    }
}
