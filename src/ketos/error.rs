//! Contains consolidated `Error` type.

use std::error::Error as StdError;
use std::fmt;

use crate::compile::CompileError;
use crate::encode::{DecodeError, EncodeError};
use crate::exec::ExecError;
use crate::io::IoError;
use crate::name::{NameDisplay, NameStore};
use crate::parser::ParseError;
use crate::restrict::RestrictError;

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
        /// Customized error value implementing `std::error::Error`
        Custom(Box<dyn StdError>),
    }
}

impl Error {
    /// Returns an `Error` value wrapping a custom error type.
    pub fn custom<E: 'static + StdError>(e: E) -> Error {
        Error::Custom(Box::new(e))
    }

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
            Error::Custom(_) => "error",
        }
    }
}

impl StdError for Error {
    fn description(&self) -> &str {
        self.description()
    }
}

#[cfg(test)]
mod test {
    use std::error::Error as StdError;
    use std::fmt;

    use super::Error;

    #[derive(Debug)]
    struct E;

    impl fmt::Display for E {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("an error occurred")
        }
    }

    impl StdError for E {
        fn description(&self) -> &str { "error" }
    }

    #[test]
    fn test_custom_error() {
        let e = Error::custom(E);
        assert_eq!(e.description(), "error");
        assert_eq!(e.to_string(), "an error occurred");
    }
}
