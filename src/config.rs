//! Various traits, types, and macros to help with configuring the editor

pub mod prelude {
    pub use std::sync::{Arc, Mutex, MutexGuard};
}

use crate::prelude::*;

pub trait Configurable<Config: ConfigPart> {
    fn update(&mut self, config: &Config);
}

pub trait ConfigPart: Build {
    type Deref: Deref<Target = Self>;
    type DerefMut: DerefMut<Target = Self>;

    /// Gives access to the global configuration
    fn global() -> Self::Deref;

    /// Gives mutable access to the global configuration
    fn global_mut() -> Self::DerefMut;

    /// Updates the local config with the given builder
    ///
    /// All [`Configurable`] items must also be updated through this method as well.
    ///
    /// [`Configurable`]: trait.Configurable.html
    fn update(&mut self, builder: Self::Builder);
}

pub trait Build: Default {
    type Builder: for<'a> Deserialize<'a> + Serialize + XInto<Self>;
}

pub struct DerefChain<D: Deref, T> {
    pub host: D,
    pub get: fn(&D::Target) -> &T,
}

impl<D: Deref, T> Deref for DerefChain<D, T> {
    type Target = T;

    fn deref(&self) -> &T {
        (self.get)(&self.host)
    }
}

pub struct DerefMutChain<D: DerefMut, T> {
    pub host: D,
    pub get: fn(&D::Target) -> &T,
    pub get_mut: fn(&mut D::Target) -> &mut T,
}

impl<D: DerefMut, T> Deref for DerefMutChain<D, T> {
    type Target = T;

    fn deref(&self) -> &T {
        (self.get)(&self.host)
    }
}

impl<D: DerefMut, T> DerefMut for DerefMutChain<D, T> {
    fn deref_mut(&mut self) -> &mut T {
        (self.get_mut)(&mut self.host)
    }
}

#[macro_export]
macro_rules! static_config {
    (
        static $global:ident;
        $builder_vis:vis struct $builder:ident;
        $config_vis:vis struct $config:ident {
            $($field_vis:vis $field:ident: $field_ty:ty = $value:expr,)*
        }
    ) => {
        static_config! {
            static $global;
            @Builder = $builder;
            $config_vis struct $config {
                $($field_vis $field: $field_ty = $value,)*
            }

            impl ConfigPart {
                fn update(this: &mut Self, builder: $builder) {
                    $(if let Some(b) = builder.$field {
                        this.$field = b;
                    })*
                }
            }
        }

        #[derive(Debug, Serialize, Deserialize)]
        $builder_vis struct $builder {
            $($field: Option<$field_ty>,)*
        }

        impl XFrom<Builder> for $config {
            fn xfrom(builder: Builder) -> Self {
                Self {
                    $($field: builder.$field.unwrap_or_else(|| $value),)*
                }
            }
        }
    };

    (
        static $global:ident;
        @Builder = $builder:ty;
        $config_vis:vis struct $config:ident {
            $($field_vis:vis $field:ident: $field_ty:ty = $value:expr,)*
        }

        impl ConfigPart {
            fn update($this:ident: &mut Self, $build_method_name:ident: $fn_builder:ty)
                $impl_body:tt
        }
    ) => {
        lazy_static::lazy_static! {
            static ref $global: Arc<Mutex<$config>> =
                Arc::new(Mutex::new(Default::default()));
        }

        $config_vis struct $config {
            $($field_vis $field: $field_ty,)*
        }

        impl ConfigPart for $config {
            type Deref = MutexGuard<'static, $config>;
            type DerefMut = MutexGuard<'static, $config>;

            fn global() -> Self::Deref { $global.lock().unwrap() }
            fn global_mut() -> Self::DerefMut { $global.lock().unwrap() }

            fn update(&mut self, builder: $builder) {
                (|$this: &mut Self, $build_method_name: $fn_builder|
                    $impl_body
                )(self, builder)
            }
        }

        impl Build for $config {
            type Builder = $builder;
        }

        impl Default for $config {
            fn default() -> Self {
                Self {
                    $($field: $value,)*
                }
            }
        }
    }
}
