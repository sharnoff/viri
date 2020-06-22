//! Helper types for separate configuration of `Mode`s
//!
//! This module is distinct from [`crate::config`], but makes heavy use of it. There are two
//! central types defined here: [`BaseConfig`] and [`ExtConfig<T>`]. The first acts as a base
//! configuration that will work for any [`Mode<T>`] (by virtue of producing [`Cmd<!>`]), whereas
//! the second allows unique extensions to that configuration made with specific generic types.
//!
//! On top of this, there's also the [`ExtendsCfg`] trait, which allows abstracting over both of
//! these with functions that produce boxed trait objects giving configurations for individual
//! modes.
//!
//! Individual modes *also* define their own versions of both the types and the trait - these are
//! all directly used to *compose* these higher-level values. As an immediate example, the
//! `ExtendsCfg` trait defines a method `insert`, which returns a boxed trait-object of
//! `insert::ExtendsCfg`. For more detail, please refer to the definitions of each of these three.
//!
// TODO: Abstract over these with macros for producing traits
//
// TODO: For an example of usage, see [`views::file`] with its `ExtConfig<views::MetaCmd<FileMeta>>`
//!
//! [`crate::config`]: ../../config/index.html
//! [`Config`]: struct.Config.html
//! [`ExtConfig<T>`]: struct.ExtConfig.html
//! [`Mode<T>`]: ../trait.Mode.html
//! [`Cmd<!>`]: ../enum.Cmd.html
//! [`views::file`]: ../../views/file/index.html
//! [`ExtendsCfg`]: trait.ExtendsCfg.html

use super::{insert, normal};
use std::ops::Deref;

mode_config_types! {
    /// The base configuration for a set of modes
    // TODO: Document
    #[derive(Default)]
    pub struct BaseConfig {
        pub insert: Config => ExtConfig<T>, impl ExtendsCfg<T>, <Ifn>,
        pub normal: Config => ExtConfig<T>, impl ExtendsCfg<T>, <NFn>,
    }

    pub struct ExtConfig<T> = ...;
    pub trait ExtendsCfg<T> {
        fn parent(&self) -> Option<Box<dyn ExtendsCfg<T>>>;
    }

    pub fn dyn_extends_cfg<...>(...) -> Box<dyn ExtendsCfg<T>>;
}

pub type ConfigParent<T> = fn() -> Box<dyn ExtendsCfg<T>>;

pub fn get_all<'a, T>(ext_cfg: Box<dyn 'a + ExtendsCfg<T>>) -> Vec<Box<dyn 'a + ExtendsCfg<T>>> {
    let mut v = match ext_cfg.parent() {
        Some(p) => get_all(p),
        None => Vec::new(),
    };

    v.insert(0, ext_cfg);
    v
}
