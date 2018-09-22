//! Performs name-based text completion using a `GlobalScope`.

use scope::{GlobalScope, MasterScope};

/// Returns a sorted list of possible name completions for the given prefix.
///
/// Returns `None` if no possible completions exist.
pub fn complete_name(word: &str, scope: &GlobalScope) -> Option<Vec<String>> {
    let mut results = Vec::new();

    for name in MasterScope::names() {
        scope.with_name(name, |name| {
            if name.starts_with(word) {
                results.push(name.to_owned());
            }
        });
    }

    scope.with_values(|values| {
        for &(name, _) in values {
            scope.with_name(name, |name| {
                if name.starts_with(word) {
                    results.push(name.to_owned());
                }
            });
        }
    });

    scope.with_macros(|macros| {
        for &(name, _) in macros {
            scope.with_name(name, |name| {
                if name.starts_with(word) {
                    results.push(name.to_owned());
                }
            });
        }
    });

    if results.is_empty() {
        None
    } else {
        results.sort();
        Some(results)
    }
}
