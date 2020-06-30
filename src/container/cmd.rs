//! Tooling for commands in colon mode
//!
//! The primary purpose of these is to allow individual `View`s to extend a common set of commands.

use super::params::set_runtime_param;

macro_rules! cmds {
    (
        $(#[$fn_doc:meta])*
        $fn_vis:vis fn $fn_name:ident(...) { ... }

        $(#[$attrs:meta])*
        $vis:vis enum $cmd:ident<'a> {
            $($name:expr $(=> @$call:ident())? $(=> $variant:ident ~ $valid:expr)?,)+
        }
    ) => {
        $(#[$attrs])*
        $vis enum $cmd<'a> {
            $($($variant { args: &'a str },)?)+
        }

        $(#[$fn_doc])*
        $fn_vis fn $fn_name<'a>(cmd: &'a str) -> Option<Result<Option<$cmd<'a>>, String>> {
            use $cmd::*;

            let splits = cmd.splitn(2, ' ').collect::<Vec<_>>();

            match &splits as &[_] {
                $(
                [$name, args] => {
                    $(Some($call(args).map(|_| None)))?
                    $(Some($valid(args).map(|_| Some($variant { args }))))?
                }
                [$name] => {
                    $(Some($call("").map(|_| None)))?
                    $(Some($valid("").map(|_| Some($variant { args: "" }))))?
                }
                )+
                _ => None,
            }
        }
    }
}

cmds! {
    pub fn try_exec_cmd(...) { ... }

    /// The set of commands from colon mode that must be handled individually by each `View`
    pub enum Cmd<'a> {
        "set" => @exec_set_cmd(),
        "setlocal" => SetLocal ~ yes_args("setlocal"),
        "q" => Quit ~ no_args("quit"),
        // "wq" => WriteQuit ~ yes_args("write-quit"),
        "q!" => ForceQuit ~ no_args("force-quit"),
        // "qa" => QuitAll ~ no_args("quit-all"),
        // "wqa" => WriteQuitAll ~ no_args("write-quit-all"),
        // "qa!" => ForceQuitAll ~ no_args("force-quit-all"),
    }
}

/// A helper function for returning an error if there are arguments to the
fn no_args(name: &'static str) -> impl Fn(&str) -> Result<(), String> {
    move |args| {
        if args == "" || args.chars().all(char::is_whitespace) {
            return Ok(());
        }

        Err(format!("error: command '{}' takes no arguments", name))
    }
}

fn yes_args(name: &'static str) -> impl Fn(&str) -> Result<(), String> {
    move |args| {
        if args == "" || args.chars().all(char::is_whitespace) {
            return Err(format!("error: command '{}' requires an argument", name));
        }

        Ok(())
    }
}

fn exec_set_cmd(args: &str) -> Result<(), String> {
    let (param, val) = parse_set_args(args)?;

    // FIXME: Unescape the string provided here
    set_runtime_param(&param, val)
}

pub fn parse_set_args<'a>(args: &'a str) -> Result<(String, String), String> {
    // We have a couple different options here.
    //
    // Typical usage of the set command either be: `set <param>=<value>` or `set <param> <value>`,
    // where `<value>` might be enclosed in single- or double-quotes.
    //
    // We'll divide this into a few bits, iterating over all of the characters to first consume the
    // parameter, then the value.

    let chars = args.chars().collect::<Vec<_>>();

    let mut i = 0;
    for &c in &chars {
        if c == ' ' || c == '=' {
            break;
        }

        i += 1;
    }

    static MALFORMED_MSG: &'static str =
        "Malformed 'set' command. Usage: `set <param>=<value>` or `set <param> <value>`";

    if i == chars.len() {
        return Err(MALFORMED_MSG.into());
    }

    let param = chars[..i].iter().collect::<String>();

    // Now we'll consume the rest of the string as the value, checking that it's been formatted
    // correctly

    // A value to indicate the types of quotes being used to enclose the value
    let quotes = match chars.get(i + 1) {
        c @ Some('\"') | c @ Some('\'') => c.cloned(),
        Some(_) => None,

        // If there aren't any characters left, we'll return - but only if the user explicitly
        // indicates they want an empty vlaue
        None if chars[i] == '=' => return Ok((param, String::new())),

        // Otherwise, chars[i] = ' ', which means that they had a trailing space after the
        // parameter, but nothing beyond that. We'll return an error indicating their mistake
        None => return Err(MALFORMED_MSG.into()),
    };

    // Shift the the index to the start of the value we're assigning - if there's quotes, we'll
    // skip an extra character to account for them
    i = match quotes {
        Some(_) => i + 2,
        None => i + 1,
    };

    if i >= chars.len() {
        return Err(MALFORMED_MSG.into());
    }

    let start = i;

    let mut closed = false;
    while i < chars.len() {
        match chars[i] {
            // A backslash to escape isn't allowed without quotes
            '\\' if quotes.is_none() => {
                return Err(
                    "Malformed 'set' command. Backslashes ('\\') can only be used inside of quotes"
                        .into(),
                );
            }
            // If there's a backslash to escape, we'll skip a couple
            '\\' => i += 2,
            q if Some(q) == quotes => {
                closed = true;
                break;
            }
            _ => i += 1,
        }
    }

    if i != chars.len() || (quotes.is_some() && !closed) {
        return Err(MALFORMED_MSG.into());
    }

    if quotes.is_some() {
        i -= 1;
    }

    // FIXME: Unescape the string provided here
    Ok((param, chars[start..i].iter().collect()))
}
