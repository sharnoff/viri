//! File management extension

use std::collections::hash_map::Entry;
use std::collections::HashMap;
use tokio::fs;
use tokio::sync::Mutex;

use crate::init::LazyInit;
use crate::macros::{extension_export, id, make_extension, Typed};

make_extension! {
    path: file,
    aliases: ["file"],
    exports: [open, record_renamed],
    init: {
        REGISTRY.initialize_with(Mutex::new(Registry {
            paths: HashMap::new(),
            info: Vec::new(),
        }));
    }
}

static REGISTRY: LazyInit<Mutex<Registry>> = LazyInit::new();

struct Registry {
    paths: HashMap<String, FileId>,
    info: Vec<Option<FileInfo>>,
}

id! {
    /// A unique, incrementing identifier for files that have been opened in this edit session
    #[derive(Typed)]
    struct FileId in [FileInfo];
}

/// The result of a successfully opened file
#[derive(Typed)]
pub struct Open {
    id: FileId,
    /// Whether the file
    created: bool,
}

enum PathStatus {
    NotAbsolute,
    NotCanonical,
    IsDir,
    WouldCreate,
    Ok,
}

/// Opens the provided file, if it exists
///
/// The provided path must be absolute; relative paths will be rejected.
#[extension_export]
pub async fn open(path: String, allow_create: bool) -> Result<Open, String> {
    match path_info(&path) {
        PathStatus::NotAbsolute => return Err(format!("Cannot open relative path {:?}", path)),
        PathStatus::NotCanonical => {
            return Err(format!("Cannot open not-canonical path {:?}", path))
        }
        PathStatus::IsDir => {
            return Err(format!(
                "Cannot open directory as file with path {:?}",
                path
            ))
        }
        PathStatus::WouldCreate => {
            if !allow_create {
                return Err(format!("Cannot open path that would create {:?}", path));
            }
        }
        PathStatus::Ok => (),
    }

    let mut registry = REGISTRY.lock().await;
    let mut created = false;

    let id = match registry.paths.entry(path.clone()) {
        Entry::Vacant(e) => {
            // If the file already exists on disk, we'll read it in.
            let content = fs::read(&path).await.unwrap_or_else(|_| {
                created = true;
                Vec::new()
            });
            let new_id = FileId(registry.info.len());
            e.insert(new_id);
            registry.info.push(Some(FileInfo::new(content)));

            new_id
        }
        Entry::Occupied(e) => {
            // If the file doesn't exist on disk, but we already have an entry open for it, we
            // shouldn't return that we created a new file. So we can keep `created = false`.
            e.get()
        }
    };

    Ok(Open { id, created })
}

#[extension_export]
pub fn record_renamed(original: String, new: String) -> Result<(), String> {
    todo!()
}

struct FileInfo {
    // obj: TextObject,
    // lines: Ranged<
    content: Ranged<TextSegment>,
    edits: History<TextSlice, SystemTime>,
}

struct TextSegment;
struct TextSlice;
