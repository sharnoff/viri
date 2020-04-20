#!/bin/sh

# cargo run -- -l log --log-level=Debug src/main.rs
cargo run -- --config-dir "$HOME/Rust/viri/test" "$HOME/Rust/viri/src/main.rs"
