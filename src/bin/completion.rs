//! Performs name-based text completion using the current `GlobalScope`.

use ketos::scope::{GlobalScope, MasterScope};
use linefeed::Completion;

/// Returns common prefix and possible completion suffixes for a given input.
pub fn complete(word: &str, scope: &GlobalScope)
        -> Option<Vec<Completion>> {
    let mut results = Vec::new();

    for name in MasterScope::get_names() {
        scope.with_name(name, |name| {
            if name.starts_with(word) {
                results.push(Completion::simple(name.to_owned()));
            }
        });
    }

    scope.with_values(|values| {
        for &(name, _) in values {
            scope.with_name(name, |name| {
                if name.starts_with(word) {
                    results.push(Completion::simple(name.to_owned()));
                }
            });
        }
    });

    scope.with_macros(|macros| {
        for &(name, _) in macros {
            scope.with_name(name, |name| {
                if name.starts_with(word) {
                    results.push(Completion::simple(name.to_owned()));
                }
            });
        }
    });

    if results.is_empty() {
        None
    } else {
        Some(results)
    }
}
