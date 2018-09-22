//! Creates an abstraction layer to I/O operations

use std::fmt::{self, Arguments};
use std::fs;
use std::io::{self, Stdout, Stderr, Write};
use std::path::{Path, PathBuf};
use std::rc::Rc;

use name::{NameDisplay, NameStore};

/// Contains global shared I/O objects
pub struct GlobalIo {
    /// Shared standard output writer
    pub stdout: Rc<SharedWrite>,
}

impl GlobalIo {
    /// Creates a `GlobalIo` instance using the given `stdout` writer.
    pub fn new(stdout: Rc<SharedWrite>) -> GlobalIo {
        GlobalIo{ stdout }
    }

    /// Creates a `GlobalIo` instance whose `stdout` ignores all output.
    pub fn null() -> GlobalIo {
        GlobalIo::new(Rc::new(Sink))
    }
}

impl Default for GlobalIo {
    /// Creates a `GlobalIo` instance using standard output writer.
    fn default() -> GlobalIo {
        GlobalIo::new(Rc::new(io::stdout()))
    }
}

/// Describes the cause of an `io::Error`.
#[derive(Debug)]
pub struct IoError {
    /// Error value
    pub err: io::Error,
    /// Path to file whose operation produced the error
    pub path: PathBuf,
    /// I/O mode that produced the error
    pub mode: IoMode,
}

impl IoError {
    /// Creates a new `IoError`.
    pub fn new(mode: IoMode, path: &Path, err: io::Error) -> IoError {
        IoError{
            mode: mode,
            path: path.to_owned(),
            err: err,
        }
    }
}

impl fmt::Display for IoError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "failed to {} file `{}`: {}",
            self.mode, self.path.display(), self.err)
    }
}

impl NameDisplay for IoError {
    fn fmt(&self, _names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// Indicates the type of I/O operation that generated an error.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum IoMode {
    /// Creating a new file
    Create,
    /// Opening an existing file
    Open,
    /// Reading data from an open file
    Read,
    /// Accessing file metadata
    Stat,
    /// Writing data to an open file
    Write,
}

impl fmt::Display for IoMode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match *self {
            IoMode::Create => "create",
            IoMode::Open => "open",
            IoMode::Read => "read",
            IoMode::Stat => "stat",
            IoMode::Write => "write",
        })
    }
}

/// A writer object that can operate using shared references.
pub trait SharedWrite {
    /// Analogous to `std::io::Write::write_all`; writes all bytes
    /// or returns an error.
    fn write_all(&self, buf: &[u8]) -> Result<(), IoError>;

    /// Analogous to `std::io::Write::write_all`; writes formatted arguments
    /// or returns an error.
    fn write_fmt(&self, fmt: Arguments) -> Result<(), IoError>;

    /// Analogous to `std::io::Write::flush`; flushes the output stream.
    fn flush(&self) -> Result<(), IoError>;
}

macro_rules! shared_write {
    ( $ty:ty => $name:expr ) => {
        impl SharedWrite for $ty {
            fn write_all(&self, buf: &[u8]) -> Result<(), IoError> {
                let mut lock = self.lock();
                Write::write_all(&mut lock, buf)
                    .map_err(|e| IoError::new(
                        IoMode::Write, Path::new($name), e))
            }

            fn write_fmt(&self, fmt: Arguments) -> Result<(), IoError> {
                let mut lock = self.lock();
                Write::write_fmt(&mut lock, fmt)
                    .map_err(|e| IoError::new(
                        IoMode::Write, Path::new($name), e))
            }

            fn flush(&self) -> Result<(), IoError> {
                let mut lock = self.lock();
                Write::flush(&mut lock)
                    .map_err(|e| IoError::new(
                        IoMode::Write, Path::new($name), e))
            }
        }
    }
}

shared_write!{ Stdout => "<stdout>" }
shared_write!{ Stderr => "<stderr>" }

/// A shared writer which sends all data into the void.
pub struct Sink;

impl SharedWrite for Sink {
    fn write_all(&self, _buf: &[u8]) -> Result<(), IoError> { Ok(()) }
    fn write_fmt(&self, _fmt: Arguments) -> Result<(), IoError> { Ok(()) }
    fn flush(&self) -> Result<(), IoError> { Ok(()) }
}

/// Wraps a `fs::File` as a shared writer, providing a path for error values.
pub struct File {
    file: fs::File,
    path: PathBuf,
}

impl File {
    /// Creates a new `File` from an open filehandle and path.
    pub fn new(file: fs::File, path: PathBuf) -> File {
        File{ file, path }
    }
}

impl SharedWrite for File {
    fn write_all(&self, buf: &[u8]) -> Result<(), IoError> {
        Write::write_all(&mut &self.file, buf)
            .map_err(|e| IoError::new(IoMode::Write, &self.path, e))
    }

    fn write_fmt(&self, fmt: Arguments) -> Result<(), IoError> {
        Write::write_fmt(&mut &self.file, fmt)
            .map_err(|e| IoError::new(IoMode::Write, &self.path, e))
    }

    fn flush(&self) -> Result<(), IoError> {
        Write::flush(&mut &self.file)
            .map_err(|e| IoError::new(IoMode::Write, &self.path, e))
    }
}
