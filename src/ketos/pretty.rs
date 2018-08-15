//! Facilities for pretty-printing `Value`s.

use std::fmt::{self, Write};

use name::{debug_names, NameStore};
use value::Value;

/// Writes a human-readable representation of a `Value` to the given `fmt::Write`.
///
/// `indent` specifies the base indentation for items contained within lists.
/// Indentation is not applied to the top level value.
pub fn pretty_print<W: Write>(w: &mut W, names: &NameStore, v: &Value, indent: u32) -> fmt::Result {
    match *v {
        Value::List(ref li) => {
            let mut iter = li.iter();

            let first = iter.next().expect("empty list value");

            let sub_indent = match *first {
                Value::Name(_) => indent + 2,
                _ => indent + 1
            };

            w.write_char('(')?;
            pretty_print(w, names, first, indent)?;

            if is_short_args(&li[1..]) {
                for v in iter {
                    w.write_char(' ')?;
                    pretty_print(w, names, v, sub_indent)?;
                }
            } else {
                while let Some(v) = iter.next() {
                    w.write_char('\n')?;
                    write_indent(w, sub_indent)?;
                    pretty_print(w, names, v, sub_indent)?;

                    // Pair keywords with their arguments
                    if let Value::Keyword(_) = *v {
                        if let Some(v) = iter.next() {
                            w.write_char(' ')?;
                            pretty_print(w, names, v, sub_indent)?;
                        }
                    }
                }
            }

            w.write_char(')')
        }
        _ => write!(w, "{}", debug_names(names, v))
    }
}

fn is_short_args(args: &[Value]) -> bool {
    args.len() <= 5 && args.iter().all(|v| {
        match *v {
            Value::List(_) => false,
            Value::String(ref s) if s.len() > 15 => false,
            _ => true
        }
    })
}

fn write_indent<W: Write>(w: &mut W, n: u32) -> fmt::Result {
    for _ in 0..n {
        w.write_char(' ')?;
    }
    Ok(())
}
