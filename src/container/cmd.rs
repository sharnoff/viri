//! Tooling for commands in colon mode
//!
//! The primary purpose of these is to allow individual `View`s to extend a common set of commands.

use super::params::set_runtime_param;

pub fn try_exec_cmd(cmd: &str) -> Option<Result<(), String>> {
    let splits = cmd.splitn(2, ' ').collect::<Vec<_>>();
    match &splits as &[_] {
        [_, _, _, ..] => unreachable!(),
        ["set", args] => Some(exec_set_cmd(args)),
        ["set"] => Some(exec_set_cmd("")),
        _ => None,
    }
}

fn exec_set_cmd(args: &str) -> Result<(), String> {
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
        None if chars[i] == '=' => return set_runtime_param(&param, "".into()),

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
    set_runtime_param(&param, chars[start..i].iter().collect())
}
