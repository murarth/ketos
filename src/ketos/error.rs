//! Contains consolidated `Error` type.

use std::error::Error as StdError;
use std::fmt;

use compile::CompileError;
use encode::{DecodeError, EncodeError};
use exec::ExecError;
use io::IoError;
use name::{NameDisplay, NameStore};
use parser::ParseError;
use restrict::RestrictError;

macro_rules! error_type {
    ( $( #[$meta:meta] )* pub enum $name:ident
            { $( $( #[$var_meta:meta] )+ $var:ident($ty:ty) , )+ } ) => {
        $( #[$meta] )*
        pub enum $name {
            $( $( #[$var_meta] )+ $var($ty) ),+
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                match *self {
                    $( $name::$var(ref e) => fmt::Display::fmt(e, f) ),+
                }
            }
        }

        impl NameDisplay for $name {
            fn fmt(&self, names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result {
                match *self {
                    $( $name::$var(ref e) => NameDisplay::fmt(e, names, f) ),+
                }
            }
        }

        $(
            impl From<$ty> for $name {
                fn from(e: $ty) -> $name {
                    $name::$var(e)
                }
            }
        )+
    }
}

error_type!{
    /// Consolidated error type; contains one of a category of errors.
    #[derive(Debug)]
    pub enum Error {
        /// Error in compiling code to bytecode
        CompileError(CompileError),
        /// Error in decoding bytecode file format
        DecodeError(DecodeError),
        /// Error in encoding bytecode file format
        EncodeError(EncodeError),
        /// Error in executing code
        ExecError(ExecError),
        /// Error in file I/O operation
        IoError(IoError),
        /// Error in scanning text or parsing syntax
        ParseError(ParseError),
        /// Code execution breached configured restrictions
        RestrictError(RestrictError),
    }
}

impl Error {
    /// Returns a string describing the nature of the error.
    pub fn description(&self) -> &'static str {
        match *self {
            Error::CompileError(_) => "compile error",
            Error::DecodeError(_) => "decode error",
            Error::EncodeError(_) => "encode error",
            Error::ExecError(_) => "execution error",
            Error::IoError(_) => "I/O error",
            Error::ParseError(_) => "parse error",
            Error::RestrictError(_) => "restriction error",
        }
    }
}

impl StdError for Error {
    fn description(&self) -> &str {
        self.description()
    }
}
