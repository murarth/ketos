//! Configuration of runtime execution restrictions
//!
//! The `RestrictConfig` instance within an execution context configures
//! the restrictions imposed on code execution. These restrictions may include
//! limiting execution time and memory consumption.
//!
//! However, use of `RestrictConfig` is not necessarily sufficient to isolate
//! an execution environment from the host system. Other steps should be taken,
//! such as:
//!
//! * Installing a `GlobalIo` instance that does not allow access to
//!   system `stdout` and `stdin` streams.
//! * Installing a `ModuleLoader` instance that restricts access to the
//!  filesystem and whitelists a small set of "safe" builtin modules.
//!
//! # Example
//!
//! ```
//! use std::rc::Rc;
//! use ketos::{Builder, GlobalIo, BuiltinModuleLoader, RestrictConfig};
//!
//! let interp = Builder::new()
//!     .restrict(RestrictConfig::strict())
//!     .io(Rc::new(GlobalIo::null()))
//!     .module_loader(Box::new(BuiltinModuleLoader))
//!     .finish();
//!
//! // ...
//! # let _ = interp;
//! ```

use std::fmt;
use std::time::Duration;

use name::{NameDisplay, NameStore};

/// Contains parameters configuring restrictions of runtime code execution
///
/// See [module-level documentation](index.html) for an example of its use.
#[derive(Clone, Debug)]
pub struct RestrictConfig {
    /// Limits the maximum execution time, beginning from a call into the
    /// virtual machine, until the topmost function returns.
    ///
    /// If the user desires to limit total execution time of multiple separate
    /// function calls, the user must track execution time and adjust this
    /// limit manually.
    pub execution_time: Option<Duration>,
    /// Limits the call stack depth during execution to a number of nested
    /// functions calls
    pub call_stack_size: usize,
    /// Limits the number of values that can be stored on the stack during
    /// execution
    pub value_stack_size: usize,
    /// Limits the maximum number of values that can be stored in a `GlobalScope`
    pub namespace_size: usize,
    /// Memory limit during execution of code.
    /// This is not a specific measure of bytes; it's more an abstract
    /// estimate of values held during execution.
    pub memory_limit: usize,
    /// Maximum size, in bits, of integer and ratio values
    pub max_integer_size: usize,
    /// Maximum nested depth of syntactical elements
    pub max_syntax_nesting: usize,
}

/// Represents an error caused by breach of runtime execution restrictions
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum RestrictError {
    /// Execution time exceeded limit
    ExecutionTimeExceeded,
    /// Call stack exceeded limit
    CallStackExceeded,
    /// Value stack exceeded limit
    ValueStackExceeded,
    /// Namespace size exceeded limit
    NamespaceSizeExceeded,
    /// Memory consumption exceeded limit
    MemoryLimitExceeded,
    /// Integer bit limit exceeded
    IntegerLimitExceeded,
    /// Nested syntax exceeded limit
    MaxSyntaxNestingExceeded,
}

impl RestrictError {
    /// Returns a string describing the error that occurred.
    pub fn description(&self) -> &'static str {
        use self::RestrictError::*;

        match *self {
            ExecutionTimeExceeded => "execution time exceeded",
            CallStackExceeded => "max call stack exceeded",
            ValueStackExceeded => "max value stack exceeded",
            NamespaceSizeExceeded => "max namespace size exceeded",
            MemoryLimitExceeded => "max memory limit exceeded",
            IntegerLimitExceeded => "integer size limit exceeded",
            MaxSyntaxNestingExceeded => "max syntax nesting exceeded",
        }
    }
}

impl fmt::Display for RestrictError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.description())
    }
}

impl NameDisplay for RestrictError {
    fn fmt(&self, _names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// Maximum size of call stack, with permissive configuration.
pub const PERMISSIVE_CALL_STACK_SIZE: usize = 1024;

/// Maximum size of value stack, in values, with permissive configuration.
pub const PERMISSIVE_VALUE_STACK_SIZE: usize = 4096;

/// Maximum size of call stack, with strict configuration.
pub const STRICT_CALL_STACK_SIZE: usize = PERMISSIVE_CALL_STACK_SIZE / 16;

/// Maximum size of value stack, in values, with strict configuration.
pub const STRICT_VALUE_STACK_SIZE: usize = PERMISSIVE_VALUE_STACK_SIZE / 16;

impl RestrictConfig {
    /// Returns a `RestrictConfig` that is most permissive.
    ///
    /// No restrictions are placed on executing code.
    pub fn permissive() -> RestrictConfig {
        RestrictConfig{
            execution_time: None,
            call_stack_size: PERMISSIVE_CALL_STACK_SIZE,
            value_stack_size: PERMISSIVE_VALUE_STACK_SIZE,
            namespace_size: usize::max_value(),
            memory_limit: usize::max_value(),
            max_integer_size: usize::max_value(),
            max_syntax_nesting: usize::max_value(),
        }
    }

    /// Returns a `RestrictConfig` that is most strict.
    ///
    /// Small programs with short runtimes should not have a problem operating
    /// within these restrictions.
    pub fn strict() -> RestrictConfig {
        RestrictConfig{
            execution_time: Some(Duration::from_millis(100)),
            call_stack_size: STRICT_CALL_STACK_SIZE,
            value_stack_size: STRICT_VALUE_STACK_SIZE,
            namespace_size: 32,
            memory_limit: STRICT_VALUE_STACK_SIZE,
            max_integer_size: 100,
            max_syntax_nesting: 32,
        }
    }
}
