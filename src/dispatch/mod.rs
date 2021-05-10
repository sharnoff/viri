//! Dynamic dispatch for internal functions & extensions/plugins
//!
//! This module provides the system for coordinating the evaluation of request- and event-handlers
//! for the entire event system within the editor. The system is implemented with channels - i.e.
//! without (much) global state.

use maplit::hashmap;
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display, Formatter};
use tokio::sync::{mpsc, oneshot};
use uuid::Uuid;

use crate::init::LazyInit;
use crate::macros::{init, require_initialized, Typed};

#[macro_use]
mod builtin;
mod load;
pub mod typed;

use load::LoadingHandler;
pub use typed::{TypeKind, TypeRepr, Typed, TypedConstruct, TypedDeconstruct, Value};

init! {
    require_initialized!(crate::runtime);

    let (tx, rx) = mpsc::unbounded_channel();
    COMMS.initialize_with(tx);
    crate::runtime::spawn(receive_all(rx));
}

/// (*Internal*) The central communication channel
static COMMS: LazyInit<mpsc::UnboundedSender<(Request, Callback)>> = LazyInit::new();

/// The primary event loop of this module, handling all [`Request`]s over [`COMMS`]
pub async fn receive_all(mut rx: mpsc::UnboundedReceiver<(Request, Callback)>) {
    use ExtensionAccess::{Builtin, Internal};
    use RequestKind::GetValue;

    let mut ns = BindingNamespace::new();

    while let Some((req, callback)) = rx.recv().await {
        match req.kind {
            /*
            EventNotify { event, value } => {
                let name = Name {
                    extension_id: req.originating_ext,
                    method: event,
                };
                let hs = match ns.handlers.get(&name) {
                    Some(h) => h,

                    // Every event that this attempts to notify on must be in the registry. If we
                    // don't find it here, that's an error
                    None => {
                        let err = format!(
                            "no registered event {:?} found for this extension to report",
                            name.method
                        );

                        // Explicitly discard the result of sending; there's nothing we can really
                        // do if it fails.
                        let _: Result<_, _> = callback.send(Err(err));
                        continue;
                    }
                };

                todo!() // send on all handlers that are mentioned here
            }
            */
            GetValue { from, arg } => {
                let access = match ns.access.get(&from.extension_id) {
                    Some(p) => p,
                    None => todo!("TODO-ERROR"),
                };

                match access {
                    Builtin => {
                        let op = match from.method.parse() {
                            Ok(op) => op,
                            Err(()) => {
                                let err = format!("no builtin function {:?}", from.method);
                                let _: Result<_, _> = callback.send(Err(err));
                                continue;
                            }
                        };

                        ns.handle_builtin(op, req.originating_ext, arg, callback);
                    }
                    Internal(_) => todo!(),
                }
            }
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Typed)]
pub struct ExtensionId(Uuid);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Typed)]
pub struct EventId(Uuid);

impl ExtensionId {
    /// Creates a new, random `Extensionid`
    fn random() -> Self {
        ExtensionId(Uuid::new_v4())
    }
}

impl EventId {
    /// Creates a new, random `EventId`
    fn random() -> Self {
        EventId(Uuid::new_v4())
    }
}

/// The name of a particular request or handler, with the extension given by its ID
#[derive(Debug, Clone, PartialEq, Eq, Hash, Typed)]
pub struct Name {
    pub extension_id: ExtensionId,
    pub method: String,
}

pub type Callback = oneshot::Sender<Result<Option<Value<'static>>, String>>;

/// An individual, internal binding request
pub struct Request {
    pub originating_ext: ExtensionId,

    /// The type of request signified
    pub kind: RequestKind,
    //
    // /// The channel over which to send the result of the operation
    // ///
    // /// There's a lot of information encoded in this, so let's go through it.
    // /// * If the return value is `Err(())`, the request was invalid
    // /// * If the return value is `Ok(None)`, the request is asynchronous
    // /// * If the return value is `Ok(Some(_))`, the output of the synchronous request was returned
    // callback: Callback,
}

pub enum RequestKind {
    // EventNotify { event: Name, value: Value<'static> },
    GetValue { from: Name, arg: Value<'static> },
}

impl Request {
    /// Spawns the request, blocking until its callback eventually receives a value
    pub async fn spawn(self) -> Result<Option<Value<'static>>, String> {
        let (tx, rx) = oneshot::channel();

        COMMS
            .send((self, tx))
            .ok()
            .expect("failed to send on `dispatch::COMMS`");
        rx.await.expect("failed to get value from request callback")
    }
}

/// The method of referring to a particular extension, once it's been loaded
enum ExtensionAccess {
    /// The singular "builtin" extension requires no additional information to handle
    Builtin,
    /// Internal extensions are given by reference, with their contents initialized at program
    /// startup
    ///
    /// These are all defined in the [`extensions`](crate::extensions) module.
    Internal(&'static crate::extensions::Extension),
}

// TODO-FEATURE: This variant will need more variants added whenever internal/HTTP bindings are
// added
/// The way to "contact" a particular extension - both to start it and to interact with it later
#[derive(Clone, Debug, Hash, PartialEq, Eq, Typed)]
enum ExtensionPath {
    /// The "builtin" extension
    Builtin,

    /// A path to an extension that's defined internally (i.e. in the [`extensions`] module)
    ///
    /// [`extensions`]: crate::extensions
    Internal(String),
}

impl Display for ExtensionPath {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use ExtensionPath::{Builtin, Internal};

        match self {
            Builtin => f.write_str("<builtin>"),
            Internal(s) => write!(f, "{} <internal>", s),
        }
    }
}

struct BindingNamespace {
    loader: LoadingHandler,

    // A unique identifier for the "builtin" extension, stored for convenience
    builtin_id: ExtensionId,

    access: HashMap<ExtensionId, ExtensionAccess>,
    ids: HashMap<ExtensionPath, ExtensionId>,
    paths: HashMap<ExtensionId, ExtensionPath>,

    // The handlers registered for each event. Events without any handlers may have no entry here
    handlers: HashMap<EventId, HashSet<Name>>,
    // The events registered by each extension
    owned_events: HashMap<ExtensionId, HashSet<EventId>>,
    // The event handlers registered by each extension
    owned_handlers: HashMap<ExtensionId, HashSet<(EventId, String)>>,

    // All of the methods provided by each extension
    registry: HashMap<ExtensionId, HashSet<String>>,
}

impl BindingNamespace {
    /// Constructs a new [`BindingNamespace`] with all of the builtin bindings provided
    fn new() -> Self {
        let builtin_id = ExtensionId(Uuid::new_v4());

        BindingNamespace {
            loader: LoadingHandler::new(builtin_id),
            builtin_id,
            access: hashmap! { builtin_id => ExtensionAccess::Builtin },
            ids: hashmap! { ExtensionPath::Builtin => builtin_id },
            paths: hashmap! { builtin_id => ExtensionPath::Builtin },
            handlers: HashMap::new(),
            owned_events: HashMap::new(),
            owned_handlers: HashMap::new(),
            registry: hashmap! { builtin_id => builtin::initial_namespace() },
        }
    }
}
