//! Syntax parsing and highlighting for the file viewer

use crate::container::params;
use crate::text::{ContentProvider, Lines, StyleRequest, StylerCallback};
use lazy_static::lazy_static;
use std::collections::BTreeMap;
use std::ops::Range;
use std::sync::{Arc, Mutex};
use syntect::highlighting::{
    self, FontStyle, HighlightState, Highlighter, RangedHighlightIterator, Theme, ThemeSet,
};
use syntect::parsing::{ParseState, ScopeStack, SyntaxSet};

static DEFAULT_THEME: &'static str = "Solarized (dark)";
static SYNTAX_DIR: &'static str = "/usr/share/viri/assets/syntax";
static THEMES_DIR: &'static str = "/usr/share/viri/assets/themes";

pub fn init() {
    require_param! {
        "theme",
    }

    load_syntax();
    load_themes();
}

lazy_static! {
    static ref SYNTAX_SET: Mutex<Option<SyntaxSet>> = Mutex::new(None);
    static ref THEMES: Mutex<Option<BTreeMap<String, Arc<Theme>>>> = Mutex::new(None);
}

fn load_syntax() {
    match SyntaxSet::load_from_folder(SYNTAX_DIR) {
        Ok(set) => *SYNTAX_SET.lock().unwrap() = Some(set),
        Err(e) => log::error!(
            "Failed to load syntax definitions from '{}': '{}'",
            SYNTAX_DIR,
            e
        ),
    }
}

fn load_themes() {
    match ThemeSet::load_from_folder(THEMES_DIR) {
        Ok(set) => {
            let set = set
                .themes
                .into_iter()
                .map(|(s, t)| (s, Arc::new(t)))
                .collect();
            *THEMES.lock().unwrap() = Some(set);
        }
        Err(e) => log::error!("Failed to load themes from '{}': '{}'", THEMES_DIR, e),
    }
}

fn to_ansi(style: highlighting::Style) -> ansi_term::Style {
    use ansi_term::Color::RGB;

    let foreground = {
        let c = style.foreground;
        Some(RGB(c.r, c.g, c.b))
    };

    let background = {
        let c = style.background;
        Some(RGB(c.r, c.g, c.b))
    };

    ansi_term::Style {
        foreground,
        background,
        is_bold: style.font_style.contains(FontStyle::BOLD),
        is_dimmed: false,
        is_italic: style.font_style.contains(FontStyle::ITALIC),
        is_underline: style.font_style.contains(FontStyle::UNDERLINE),
        is_blink: false,
        is_reverse: false,
        is_hidden: false,
        is_strikethrough: false,
    }
}

/// Produces the callback for styling text or an error to display to the user, if applicable
///
/// Any returned error will have already been logged in some form, so the caller need not repeat
/// this.
pub fn styler_callback(file_ext: &str) -> Result<StylerCallback, Option<String>> {
    let theme_name = match params::get_runtime_param("theme") {
        Some(name) => name,
        None => DEFAULT_THEME.into(),
    };

    let syntax_guard = SYNTAX_SET.lock().unwrap();
    let syntax_ref = match syntax_guard.as_ref() {
        // If the syntax set isn't present, we failed to load it earlier - we'll give the user an
        // error here
        None => {
            let msg = format!("Cannot highlight; failed to load syntax set");
            log::warn!("{}", msg);
            return Err(Some(msg));
        }
        // Otherwise, we'll try to find the syntax definition we're looking for
        Some(set) => match set.find_syntax_by_extension(file_ext) {
            // If we can't find the syntax reference we want, this isn't *really* an error in most
            // cases, so we'll just log it and return no error message.
            None => {
                log::info!(
                    "Cannot find syntax reference for file extension '{}'",
                    file_ext
                );
                return Err(None);
            }
            // Otherwise, everything's good! We'll return
            Some(syntax) => syntax,
        },
    };

    // Now that we have the syntax reference, we'll try to get the theme

    let theme_guard = THEMES.lock().unwrap();
    let theme = match theme_guard.as_ref() {
        // If the themes aren't present, we failed to load them earlier - we'll give the user an
        // error here
        None => {
            let msg = format!("Cannot highlight; failed to load theme set");
            log::warn!("{}", msg);
            return Err(Some(msg));
        }
        // Otherwise, we'll try to find the theme we're looking for
        Some(set) => match set.get(&theme_name) {
            // If we can't find it, this is definitely an error - we'll let the user know
            None => {
                let msg = format!(
                    "Cannot highlight; cannot find theme with name '{}'",
                    theme_name
                );
                log::warn!("{}", msg);
                return Err(Some(msg));
            }
            // Otherwise, we're all good!
            Some(theme) => theme.clone(),
        },
    };

    let parse_state = ParseState::new(syntax_ref);
    let highlighter = Highlighter::new(&theme);

    // And now we can drop the guards because we don't need them anymore

    drop((syntax_guard, theme_guard));

    let ctx = CallbackContext {
        states: Arc::new(Mutex::new(vec![Some((
            parse_state,
            HighlightState::new(&highlighter, ScopeStack::new()),
        ))])),
        theme,
    };

    Ok(Box::new(move |lines, req| ctx.handle_request(lines, req)))
}

struct CallbackContext {
    // The parse- and highlight-state at the start of each line
    //
    // The length of this list *always* gives the states that are valid. Note that values of `None`
    // indicate that the parsing failed at some earlier point (due to being unable to access the
    // line as a string), so no highlighting is done beyond that point.
    //
    // NOTE: We could store the `ScopeStack`s instead of highlight states, which might be more
    // memory efficient - this should be explored further.
    //
    // Info: https://docs.rs/syntect/4.2.0/syntect/highlighting/struct.HighlightState.html#caching
    states: Arc<Mutex<Vec<Option<(ParseState, HighlightState)>>>>,
    // A reference to the theme so that we can construct a highlighter for short-term use
    theme: Arc<Theme>,
}

// We implement `Send` and `Sync` here because the callback *is* properly synchronized through the
// internal locks, as is required for the closure containing it to implement Send + Sync
unsafe impl Send for CallbackContext {}
unsafe impl Sync for CallbackContext {}

impl CallbackContext {
    fn handle_request(
        &self,
        lines: &Lines,
        req: StyleRequest,
    ) -> Vec<Vec<(ansi_term::Style, Range<usize>)>> {
        // We can safely unwrap the syntax set because it'll never go from `Some` to `None` and we needed
        // it in order to construct this type.
        let syntax_set_guard = SYNTAX_SET.lock().unwrap();
        let syntax_set = syntax_set_guard.as_ref().unwrap();

        let mut states = self.states.lock().unwrap();

        // We're guaranteed to have states.len() >= 0, so we'
        let start = req.first_todo.min(states.len());

        // We truncate to length equal to `start+1` because each index in `states` gives the states
        // if we were to *start* at that line.
        states.truncate(start + 1);

        // Generate the highlighter from a reference to the theme
        let highlighter = Highlighter::new(&self.theme);

        // For each line in start..=req.requested, we'll update the styling - only storing the
        // values if they've actually been requested.
        let mut styles = Vec::with_capacity(1 + req.requested - req.first_todo);
        let line_range = start..=req.requested;
        for (idx, line) in line_range.clone().zip(lines.iter(line_range)) {
            let line_str = line.try_as_str();

            let (mut parse_state, mut hl_state) = match states.last().unwrap().clone() {
                Some((p, h)) if line_str.is_some() => (p, h),
                // If we're given `None`, the parsing/highlighting had a previous failure. We'll
                // just continue
                _ => {
                    if idx >= req.first_todo {
                        styles.push(Vec::new());
                    }
                    states.push(None);
                    continue;
                }
            };

            let line_str = line_str.unwrap();

            // Parse the entire line
            let stack_ops = parse_state.parse_line(line_str, &syntax_set);
            let ranges =
                RangedHighlightIterator::new(&mut hl_state, &stack_ops, line_str, &highlighter)
                    .map(|(style, _, range)| (to_ansi(style), range))
                    .collect();

            if idx >= req.first_todo {
                styles.push(ranges);
            }

            states.push(Some((parse_state, hl_state)));
        }

        styles
    }
}
