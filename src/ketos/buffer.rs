//! Provides a code buffer to help with implementing an interactive REPL

use bytecode::Code;
use error::Error;
use interpreter::Interpreter;
use parser::ParseErrorKind;
use value::Value;

/// Buffers potentially incomplete input code
#[derive(Clone, Debug)]
pub struct CodeBuffer {
    buffer: String,
}

impl CodeBuffer {
    /// Creates a `CodeBuffer` with an empty buffer
    pub fn new() -> CodeBuffer {
        CodeBuffer{
            buffer: String::new(),
        }
    }

    /// Clears the input buffer.
    pub fn clear(&mut self) {
        self.buffer.clear();
    }

    /// Feeds some input to the buffer.
    ///
    /// Input should be terminated with a newline (`'\n'`).
    ///
    /// Compilation will be attempted with the given interpreter. If parsing
    /// fails because more input is required, `Ok(MoreResult::More(_))`
    /// will be returned, indicating the reason input is incomplete.
    ///
    /// If some other error is encountered, it is returned. Otherwise,
    /// `Ok(MoreResult::Complete(_))` is returned with compiled expressions.
    ///
    /// If either `Ok(MoreResult::Complete(_))` or `Err(_)` is returned,
    /// the input buffer is cleared after compiling.
    pub fn feed_compile(&mut self, interp: &Interpreter, input: &str)
            -> Result<MoreResult<Vec<Code>>, Error> {
        self.buffer.push_str(input);

        let res = interp.compile_exprs(&self.buffer);
        self.more_result(res)
    }

    /// Feeds some input to the buffer.
    ///
    /// Like `feed_compile`, but the input is only parsed.
    pub fn feed_parse(&mut self, interp: &Interpreter, input: &str)
            -> Result<MoreResult<Vec<Value>>, Error> {
        self.buffer.push_str(input);

        let res = interp.parse_exprs(&self.buffer, None);
        self.more_result(res)
    }

    fn more_result<T>(&mut self, result: Result<T, Error>)
            -> Result<MoreResult<T>, Error> {
        match result {
            Ok(v) => {
                self.buffer.clear();
                Ok(MoreResult::Complete(v))
            }
            Err(Error::ParseError(ref e)) if e.kind == ParseErrorKind::MissingCloseParen => {
                Ok(MoreResult::More(More::Paren))
            }
            Err(Error::ParseError(ref e)) if e.kind == ParseErrorKind::UnterminatedComment => {
                Ok(MoreResult::More(More::Comment))
            }
            Err(Error::ParseError(ref e)) if e.kind == ParseErrorKind::UnterminatedString => {
                Ok(MoreResult::More(More::String))
            }
            Err(Error::ParseError(ref e)) if e.kind == ParseErrorKind::DocCommentEof => {
                Ok(MoreResult::More(More::DocComment))
            }
            Err(e) => {
                self.buffer.clear();
                Err(e)
            }
        }
    }
}

/// Indicates whether an operation has completed or more input is required
#[derive(Debug)]
pub enum MoreResult<T> {
    /// Successful completion result
    Complete(T),
    /// More input required
    More(More),
}

/// Indicates the cause of incomplete input
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum More {
    /// Open block comment (`#| ... |#`)
    Comment,
    /// Open doc-comment
    DocComment,
    /// Open parentheses
    Paren,
    /// Open string
    String,
}

impl More {
    /// Returns a character corresponding to each value
    pub fn as_char(&self) -> char {
        match *self {
            More::Comment => '#',
            More::DocComment => ';',
            More::Paren => '(',
            More::String => '"',
        }
    }
}

#[cfg(test)]
mod test {
    use interpreter::Interpreter;
    use super::{CodeBuffer, More, MoreResult};

    #[test]
    fn test_code_buffer() {
        let interp = Interpreter::new();
        let mut buf = CodeBuffer::new();

        assert_matches!(buf.feed_parse(&interp, "(foo\n"),
            Ok(MoreResult::More(More::Paren)));
        assert_matches!(buf.feed_parse(&interp, "bar)\n"),
            Ok(MoreResult::Complete(_)));

        assert_matches!(buf.feed_parse(&interp, "\"foo\n"),
            Ok(MoreResult::More(More::String)));
        assert_matches!(buf.feed_parse(&interp, "bar\"\n"),
            Ok(MoreResult::Complete(_)));

        assert_matches!(buf.feed_compile(&interp, "(foo\n"),
            Ok(MoreResult::More(More::Paren)));
        assert_matches!(buf.feed_compile(&interp, "bar)\n"),
            Ok(MoreResult::Complete(_)));

        assert_matches!(buf.feed_compile(&interp, "#| foo\n"),
            Ok(MoreResult::More(More::Comment)));
        assert_matches!(buf.feed_compile(&interp, "bar |#\n"),
            Ok(MoreResult::Complete(_)));

        assert_matches!(buf.feed_compile(&interp, ";; foo\n"),
            Ok(MoreResult::More(More::DocComment)));
        assert_matches!(buf.feed_compile(&interp, ";; bar\n"),
            Ok(MoreResult::More(More::DocComment)));
        assert_matches!(buf.feed_compile(&interp, "(define (baz) ())\n"),
            Ok(MoreResult::Complete(_)));
    }
}
