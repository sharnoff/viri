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

#[cfg(test)]
mod tests {
    //! This test is more of an integration test; it checks that a sort of architecture will be
    //! accepted by the compiler so that we can later use it in the editor if need be. As such,
    //! there are two different sub-modules used here in order to simulate the required behavior.
    //!
    //! This test takes the role of an arbitrary module within the structure of the crate, so it
    //! makes no references to the parent module directly.

    use crate::{
        config::{Build, ConfigPart},
        event::KeyEvent,
        mode::config::{BaseConfig, ConfigParent, ExtConfig, ExtendsCfg},
        mode::{self, insert, Cmd},
        trie::Trie,
        utils::{Never, XFrom, XInto},
    };
    use lazy_static::lazy_static;
    use serde::{Deserialize, Serialize};
    use std::sync::{Arc, Mutex, MutexGuard};

    mod first {
        use super::*;

        #[derive(Clone, Serialize, Deserialize)]
        pub enum MetaFst<T> {
            Foo,
            Other(T),
        }

        impl<T> XFrom<MetaFst<Never>> for MetaFst<T> {
            fn xfrom(meta: MetaFst<Never>) -> MetaFst<T> {
                match meta {
                    MetaFst::Foo => MetaFst::Foo,
                    MetaFst::Other(t) => t.xinto(),
                }
            }
        }

        #[derive(Serialize, Deserialize)]
        pub struct ExtBuilder {
            insert: insert::ExtBuilder<MetaFst<Never>>,
        }

        lazy_static! {
            static ref GLOBAL: Arc<Mutex<ExtConfig<MetaFst<Never>>>> =
                Arc::new(Mutex::new(Default::default()));
        }

        impl ConfigPart for ExtConfig<MetaFst<Never>> {
            type Deref = MutexGuard<'static, Self>;
            type DerefMut = MutexGuard<'static, Self>;

            fn global() -> Self::Deref {
                GLOBAL.lock().unwrap()
            }
            fn global_mut() -> Self::DerefMut {
                GLOBAL.lock().unwrap()
            }

            fn update(&mut self, builder: ExtBuilder) {
                self.insert.update(builder.insert);
            }
        }

        impl Build for ExtConfig<MetaFst<Never>> {
            type Builder = ExtBuilder;
        }

        impl Default for ExtConfig<MetaFst<Never>> {
            fn default() -> Self {
                Self {
                    parent: ConfigParent::Base(|| Box::new(BaseConfig::global())),
                    insert: Default::default(),
                }
            }
        }

        impl XFrom<ExtBuilder> for ExtConfig<MetaFst<Never>> {
            fn xfrom(builder: ExtBuilder) -> Self {
                Self {
                    parent: ConfigParent::Base(|| Box::new(BaseConfig::global())),
                    insert: builder.insert.xinto(),
                }
            }
        }

        impl<T> ExtendsCfg<MetaFst<T>> for ExtConfig<MetaFst<Never>> {
            fn insert<'a>(&'a self) -> Box<dyn 'a + insert::ExtendsCfg<MetaFst<T>>> {
                Box::new(&self.insert)
            }
        }

        impl<T> insert::ExtendsCfg<MetaFst<T>> for insert::ExtConfig<MetaFst<Never>> {
            fn keys(&self) -> Trie<KeyEvent, Vec<Cmd<MetaFst<T>>>> {
                Trie::from_iter(
                    self.keys
                        .iter_all_prefix(&[])
                        .map(|(keys, cmds)| (Vec::from(keys), cmds.clone().xinto())),
                )
            }
        }
    }

    mod second {
        use super::*;
        use first::MetaFst;

        #[derive(Clone, Serialize, Deserialize)]
        pub enum MetaSnd {
            Bar,
        }

        #[derive(Serialize, Deserialize)]
        pub struct ExtBuilder {
            insert: insert::ExtBuilder<MetaFst<MetaSnd>>,
        }

        lazy_static! {
            static ref GLOBAL: Arc<Mutex<ExtConfig<MetaFst<MetaSnd>>>> =
                Arc::new(Mutex::new(Default::default()));
        }

        impl ConfigPart for ExtConfig<MetaFst<MetaSnd>> {
            type Deref = MutexGuard<'static, Self>;
            type DerefMut = MutexGuard<'static, Self>;

            fn global() -> Self::Deref {
                GLOBAL.lock().unwrap()
            }
            fn global_mut() -> Self::DerefMut {
                GLOBAL.lock().unwrap()
            }

            fn update(&mut self, builder: ExtBuilder) {
                self.insert.update(builder.insert);
            }
        }

        impl Build for ExtConfig<MetaFst<MetaSnd>> {
            type Builder = ExtBuilder;
        }

        impl Default for ExtConfig<MetaFst<MetaSnd>> {
            fn default() -> Self {
                Self {
                    parent: ConfigParent::Ext(|| Box::new(<ExtConfig<MetaFst<Never>>>::global())),
                    insert: Default::default(),
                }
            }
        }

        impl XFrom<MetaFst<MetaSnd>> for MetaFst<MetaSnd> {
            fn xfrom(meta: MetaFst<MetaSnd>) -> Self {
                meta
            }
        }

        impl insert::ExtendsCfg<MetaFst<MetaSnd>> for insert::ExtConfig<MetaFst<MetaSnd>> {
            fn keys(&self) -> Trie<KeyEvent, Vec<Cmd<MetaFst<MetaSnd>>>> {
                Trie::from_iter(
                    self.keys
                        .iter_all_prefix(&[])
                        .map(|(keys, cmds)| (Vec::from(keys), cmds.clone().xinto())),
                )
            }
        }

        impl ExtendsCfg<MetaFst<MetaSnd>> for ExtConfig<MetaFst<MetaSnd>> {
            fn insert<'a>(&'a self) -> Box<dyn 'a + insert::ExtendsCfg<MetaFst<MetaSnd>>> {
                Box::new(&self.insert)
            }
        }

        impl XFrom<ExtBuilder> for ExtConfig<MetaFst<MetaSnd>> {
            fn xfrom(builder: ExtBuilder) -> Self {
                Self {
                    parent: ConfigParent::Ext(|| Box::new(<ExtConfig<MetaFst<Never>>>::global())),
                    insert: builder.insert.xinto(),
                }
            }
        }
    }
}
