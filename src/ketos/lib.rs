//! Ketos
//!
//! Lisp dialect. Or maybe Lisp-inspired something-or-other.

#![deny(missing_docs)]

extern crate byteorder;
extern crate num;
extern crate rand;

pub use compile::CompileError;
pub use encode::{DecodeError, EncodeError};
pub use error::Error;
pub use exec::ExecError;
pub use function::Arity;
pub use interpreter::Interpreter;
pub use integer::{Integer, Ratio};
pub use io::IoError;
pub use module::{BuiltinModuleLoader, FileModuleLoader, Module, ModuleBuilder, ModuleLoader};
pub use name::{Name, NameStore};
pub use parser::{ParseError, ParseErrorKind};
pub use scope::{GlobalScope, Scope};
pub use value::{ForeignValue, FromValue, FromValueRef, Value};

pub mod bytecode;
pub mod compile;
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
pub mod rc_vec;
pub mod scope;
mod string;
pub mod string_fmt;
pub mod value;

mod mod_code;
mod mod_math;
mod mod_random;
