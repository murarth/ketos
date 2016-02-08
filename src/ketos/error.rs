//! Contains consolidated `Error` type.

use std::fmt;

use compile::CompileError;
use encode::{DecodeError, EncodeError};
use exec::ExecError;
use io::IoError;
use parser::ParseError;

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
    }
}
