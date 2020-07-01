//! Macros for use in the file `View`

macro_rules! params {
    (
        $(#[$attrs:meta])*
        $vis:vis struct $name:ident {
            $($field:ident: $field_ty:ty = $default:expr,)*
        }
    ) => {
        $(#[$attrs])*
        $vis struct $name {
            $($field: Option<$field_ty>,)*
        }

        macro_rules! get_param {
            $(
            ($view:expr, $field) => {{
                use $crate::container::params::get_runtime_param;
                use std::str::FromStr;

                match $view.handler.executor().params.$field.as_ref() {
                    Some(v) => v.clone(),
                    None => match get_runtime_param(stringify!($field)) {
                        Some(s) => <$field_ty>::from_str(&s).unwrap(),
                        None => $default,
                    }
                }
            }};
            )*
        }

        fn register_params() {
            require_param! {
                $(stringify!($field) => try_parse::<$field_ty>,)*
            }
        }

        impl View {
            fn try_set_local(&mut self, args: &str) -> Result<(), String> {
                let (param, val) = container::cmd::parse_set_args(args)?;

                match &param as &str {
                    $(
                    stringify!($field) => self.handler.executor_mut().params.$field = Some(<$field_ty>::from_str(&val).map_err(|e| e.to_string())?),
                    )*
                    _ => return Err(format!("Unknown local parameter '{}'", param)),
                }

                Ok(())
            }
        }
    }
}

