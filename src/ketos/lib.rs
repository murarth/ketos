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
#![allow(clippy::new_without_default)]
#![allow(clippy::new_without_default_derive)]
#![allow(clippy::float_cmp)]

extern crate byteorder;
extern crate num;
extern crate rand;
#[cfg(feature = "serde")] extern crate serde;

#[cfg(test)]
#[macro_use] extern crate assert_matches;

pub use crate::bytecode::Code;
pub use crate::bytes::Bytes;
pub use crate::completion::complete_name;
pub use crate::compile::CompileError;
pub use crate::encode::{DecodeError, EncodeError};
pub use crate::error::Error;
pub use crate::exec::{Context, ExecError, panic, panic_none};
pub use crate::function::Arity;
pub use crate::interpreter::{Builder, Interpreter};
pub use crate::integer::{Integer, Ratio};
pub use crate::io::{File, GlobalIo, IoError, SharedWrite};
pub use crate::module::{BuiltinModuleLoader, FileModuleLoader, Module, ModuleBuilder, ModuleLoader};
pub use crate::name::{Name, NameStore};
pub use crate::parser::{ParseError, ParseErrorKind};
pub use crate::restrict::{RestrictConfig, RestrictError};
pub use crate::run::run_code;
pub use crate::scope::{GlobalScope, Scope};
pub use crate::structs::{StructDef, StructValue};
pub use crate::trace::{clear_traceback, get_traceback, set_traceback, take_traceback, Trace};
pub use crate::value::{ForeignValue, FromValue, FromValueRef, Value};
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
