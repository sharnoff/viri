//! Syntax parsing and highlighting for the file viewer

use lazy_static::lazy_static;
use std::sync::Mutex;
use syntect::highlighting::ThemeSet;
use syntect::parsing::{SyntaxSet, SyntaxSetBuilder};

pub fn init() {
    load_syntax();
    load_themes();
}

lazy_static! {
    static ref SYNTAX_SET: Mutex<Option<SyntaxSet>> = Mutex::new(None);
    static ref THEMES: Mutex<Option<ThemeSet>> = Mutex::new(None);
}

fn load_syntax() {
    let builder = SyntaxSetBuilder::new();
    // TODO: Load definitions
    *SYNTAX_SET.lock().unwrap() = Some(builder.build());
}

fn load_themes() {
    // todo!();
}
