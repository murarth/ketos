//! Ketos is a Lisp dialect functional programming language, designed to be
//! a scripting and extension language for Rust programs.
//!
//! ```
//! use ketos::{Interpreter, FromValueRef};
//!
//! // Create an interpreter.
//! let interp = Interpreter::new();
//!
//! // Define a function.
//! interp.run_code(r#"
//!     (define (foo a)
//!       (* a 2))
//!     "#, None).unwrap();
//!
//! // Call the function.
//! let result = interp.call("foo", vec![123.into()]).unwrap();
//!
//! // Get a Rust value back.
//! let n = i32::from_value_ref(&result).unwrap();
//!
//! assert_eq!(n, 246);
//! ```
//!
//! See `examples/` for more examples on interacting with the Ketos interpreter.

#![deny(missing_docs)]

extern crate byteorder;
extern crate num;
extern crate rand;
#[cfg(feature = "serde")] extern crate serde;

#[cfg(test)]
#[macro_use] extern crate assert_matches;

pub use bytecode::Code;
pub use bytes::Bytes;
pub use completion::complete_name;
pub use compile::CompileError;
pub use encode::{DecodeError, EncodeError};
pub use error::Error;
pub use exec::{Context, ExecError, panic, panic_none};
pub use function::Arity;
pub use interpreter::{Builder, Interpreter};
pub use integer::{Integer, Ratio};
pub use io::{File, GlobalIo, IoError, SharedWrite};
pub use module::{BuiltinModuleLoader, FileModuleLoader, Module, ModuleBuilder, ModuleLoader};
pub use name::{Name, NameStore};
pub use parser::{ParseError, ParseErrorKind};
pub use restrict::{RestrictConfig, RestrictError};
pub use run::run_code;
pub use scope::{GlobalScope, Scope};
pub use structs::{StructDef, StructValue};
pub use trace::{clear_traceback, get_traceback, set_traceback, take_traceback, Trace};
pub use value::{ForeignValue, FromValue, FromValueRef, Value};
#[cfg(feature = "serde")] pub use value_decode::decode_value;
#[cfg(feature = "serde")] pub use value_encode::encode_value;

#[macro_use] pub mod any;
pub mod args;
pub mod bytecode;
pub mod bytes;
pub mod completion;
pub mod compile;
mod const_fold;
pub mod encode;
pub mod error;
pub mod exec;
pub mod function;
pub mod integer;
pub mod interpreter;
pub mod io;
pub mod lexer;
pub mod module;
pub mod name;
pub mod parser;
pub mod pretty;
pub mod restrict;
pub mod rc_vec;
pub mod run;
pub mod scope;
mod string;
pub mod string_fmt;
pub mod structs;
pub mod trace;
pub mod value;
#[cfg(feature = "serde")] pub mod value_decode;
#[cfg(feature = "serde")] pub mod value_encode;

mod mod_code;
mod mod_math;
mod mod_random;
