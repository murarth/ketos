//! Performs name-based text completion using the current `GlobalScope`.

use ketos::scope::{GlobalScope, MasterScope};

/// Returns common prefix and possible completion suffixes for a given input.
pub fn complete(text: &str, start: usize, end: usize, scope: &GlobalScope) -> Option<(String, Vec<String>)> {
    // Don't attempt to complete when the input is empty
    if text.chars().all(|c| c.is_whitespace()) {
        return None;
    }

    let text = &text[start..end];
    let prefix_len = text.len();
    let mut results = Vec::new();

    for name in MasterScope::get_names() {
        scope.with_name(name, |name| {
            if name.starts_with(text) {
                results.push(name[prefix_len..].to_owned());
            }
        });
    }

    scope.with_values(|values| {
        for &(name, _) in values {
            scope.with_name(name, |name| {
                if name.starts_with(text) {
                    results.push(name[prefix_len..].to_owned());
                }
            });
        }
    });

    scope.with_macros(|macros| {
        for &(name, _) in macros {
            scope.with_name(name, |name| {
                if name.starts_with(text) {
                    results.push(name[prefix_len..].to_owned());
                }
            });
        }
    });

    if results.is_empty() {
        None
    } else {
        let prefix = common_prefix(&results);
        Some((prefix, results))
    }
}

/// Returns the (possibly empty) common prefix of the given strings.
/// Input strings must be non-empty.
fn common_prefix(strs: &[String]) -> String {
    assert!(!strs.is_empty());

    let mut prefix: String = strs[0].clone();

    for c in strs[1..].iter() {
        while !c.starts_with(&prefix) {
            prefix.pop();
        }

        if prefix.is_empty() {
            break;
        }
    }

    prefix
}
