//! Parses a series of `lexer` tokens into a code expression.

use std::borrow::Cow::{self, Borrowed, Owned};
use std::collections::HashMap;
use std::fmt;
use std::path::PathBuf;

use bytes::Bytes;
use error::Error;
use exec::Context;
use integer::{Integer, Ratio};
use lexer::{Lexer, Span, Token};
use name::{get_standard_name_for, standard_names, Name, NameDisplay, NameStore};
use restrict::RestrictError;
use string;
use value::Value;

const MODULE_DOC_COMMENT: &str = ";;;";

/// Parses a stream of tokens into an expression.
pub struct Parser<'a, 'lex> {
    lexer: Lexer<'lex>,
    ctx: &'a Context,
    name_cache: HashMap<&'lex str, Name>,
    cur_token: Option<(Span, Token<'lex>)>,
}

/// Represents an error in parsing input.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ParseError {
    /// Span of source code which caused the error
    pub span: Span,
    /// Kind of error generated
    pub kind: ParseErrorKind,
}

impl ParseError {
    /// Creates a new `ParseError`.
    pub fn new(span: Span, kind: ParseErrorKind) -> ParseError {
        ParseError{ span, kind }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.kind, f)
    }
}

impl NameDisplay for ParseError {
    fn fmt(&self, _names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// Describes the kind of error encountered in parsing.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum ParseErrorKind {
    /// Doc comment followed by incompatible token
    CannotDocumentItem,
    /// Doc comment at end-of-file
    DocCommentEof,
    /// Error in parsing literal
    InvalidLiteral,
    /// Error in parsing token
    InvalidToken,
    /// Invalid character in byte or byte string literal
    InvalidByte(char),
    /// Invalid escape sequence in byte or byte string literal
    InvalidByteEscape(char),
    /// Invalid character in input
    InvalidChar(char),
    /// Invalid character in numeric escape sequence `\xNN` or `\u{NNNN}`
    InvalidNumericEscape(char),
    /// Error parsing literal string into value
    LiteralParseError,
    /// Missing closing parenthesis
    MissingCloseParen,
    /// More commas than backquotes
    UnbalancedComma,
    /// Unexpected end-of-file
    UnexpectedEof,
    /// Unexpected token
    UnexpectedToken{
        /// Token or category of token expected
        expected: &'static str,
        /// Token found
        found: &'static str,
    },
    /// Unrecognized character escape
    UnknownCharEscape(char),
    /// Unmatched `)`
    UnmatchedParen,
    /// Unterminated character constant
    UnterminatedChar,
    /// Unterminated block comment
    UnterminatedComment,
    /// Unterminated string constant
    UnterminatedString,
}

impl fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ParseErrorKind::CannotDocumentItem =>
                f.write_str("doc comment precedes item that cannot be documented"),
            ParseErrorKind::DocCommentEof => f.write_str("doc comment at end-of-file"),
            ParseErrorKind::InvalidLiteral => f.write_str("invalid numeric literal"),
            ParseErrorKind::InvalidToken => f.write_str("invalid token"),
            ParseErrorKind::InvalidByte(ch) =>
                write!(f, "byte literal must be ASCII: {:?}", ch),
            ParseErrorKind::InvalidByteEscape(ch) =>
                write!(f, "invalid escape sequence in byte literal: {:?}", ch),
            ParseErrorKind::InvalidChar(ch) =>
                write!(f, "invalid character: {:?}", ch),
            ParseErrorKind::InvalidNumericEscape(ch) =>
                write!(f, "invalid character in escape sequence: {:?}", ch),
            ParseErrorKind::LiteralParseError => f.write_str("literal parse error"),
            ParseErrorKind::MissingCloseParen => f.write_str("missing close paren"),
            ParseErrorKind::UnbalancedComma => f.write_str("unbalanced ` and ,"),
            ParseErrorKind::UnexpectedEof => f.write_str("unexpected end-of-file"),
            ParseErrorKind::UnexpectedToken{expected, found} =>
                write!(f, "expected {}; found {}", expected, found),
            ParseErrorKind::UnknownCharEscape(ch) =>
                write!(f, "unknown char escape: {:?}", ch),
            ParseErrorKind::UnmatchedParen => f.write_str("unmatched `)`"),
            ParseErrorKind::UnterminatedChar => f.write_str("unterminated char constant"),
            ParseErrorKind::UnterminatedComment => f.write_str("unterminated block comment"),
            ParseErrorKind::UnterminatedString => f.write_str("unterminated string constant"),
        }
    }
}

enum Group<'lex> {
    /// Positive indicates a number of backticks,
    /// negative indicates a number of commas.
    Backticks(i32),
    CommaAt,
    /// Number of quotes preceding group.
    /// If zero, this is an unquoted parentheses group.
    Quotes(u32),
    /// Values in a parenthetical expression
    Parens(Vec<Value>, Option<(Span, &'lex str)>),
}

impl<'a, 'lex> Parser<'a, 'lex> {
    /// Creates a new `Parser` using the given `Lexer`.
    /// Identifiers received from the lexer will be inserted into the given context.
    pub fn new(ctx: &'a Context, lexer: Lexer<'lex>) -> Parser<'a, 'lex> {
        Parser{
            lexer: lexer,
            ctx: ctx,
            name_cache: HashMap::new(),
            cur_token: None,
        }
    }

    /// Skips the "shebang" line of a source file.
    pub fn skip_shebang(&mut self) {
        self.lexer.skip_shebang();
    }

    /// Parses an expression from the input stream.
    pub fn parse_expr(&mut self) -> Result<Value, Error> {
        let mut stack = Vec::new();
        let mut total_backticks = 0;

        loop {
            if stack.len() >= self.ctx.restrict().max_syntax_nesting {
                return Err(From::from(RestrictError::MaxSyntaxNestingExceeded));
            }

            let mut doc = self.read_doc_comment()?;

            let (sp, tok) = self.next()?;

            let r = match tok {
                Token::DocComment(_) =>
                    return Err(From::from(ParseError::new(
                        doc.unwrap().0, ParseErrorKind::CannotDocumentItem))),
                Token::LeftParen => {
                    if let Some((doc_sp, _)) = doc {
                        match self.peek()? {
                            (_, Token::Name("const")) |
                            (_, Token::Name("define")) |
                            (_, Token::Name("lambda")) |
                            (_, Token::Name("macro")) |
                            (_, Token::Name("struct"))
                                => (),
                            _ => return Err(From::from(ParseError::new(
                                doc_sp, ParseErrorKind::CannotDocumentItem)))
                        }
                    }

                    stack.push(Group::Parens(Vec::new(), doc.take()));
                    continue;
                }
                Token::RightParen => {
                    let group = stack.pop().ok_or_else(
                        || ParseError::new(sp, ParseErrorKind::UnmatchedParen))?;

                    match group {
                        Group::Parens(values, doc) =>
                            insert_doc_comment(values, doc)
                                .map_err(From::from),
                        _ => Err(From::from(ParseError::new(sp,
                            ParseErrorKind::UnexpectedToken{
                                expected: "expression",
                                found: ")",
                            })))
                    }
                }
                Token::Float(f) => parse_float(f)
                    .map(Value::Float)
                    .map_err(|kind| From::from(ParseError::new(sp, kind))),
                Token::Integer(i, base) => parse_integer(self.ctx, i, base, sp)
                    .map(Value::Integer),
                Token::Ratio(r) => parse_ratio(self.ctx, r, sp)
                    .map(Value::Ratio),
                Token::Char(ch) => parse_char(ch)
                    .map(Value::Char).map_err(From::from),
                Token::String(s) => parse_string(s)
                    .map(|s| s.into()).map_err(From::from),
                Token::Byte(b) => parse_byte(b)
                    .map(|v| v.into()).map_err(From::from),
                Token::Bytes(b) => parse_bytes(b)
                    .map(Value::Bytes).map_err(From::from),
                Token::Path(p) => parse_path(p)
                    .map(|p| p.into()).map_err(From::from),
                Token::Name(name) => Ok(self.name_value(name)),
                Token::Keyword(name) => Ok(Value::Keyword(self.add_name(name))),
                Token::BackQuote => {
                    total_backticks += 1;
                    if let Some(&mut Group::Backticks(ref mut n)) = stack.last_mut() {
                        *n += 1;
                        continue;
                    }
                    stack.push(Group::Backticks(1));
                    continue;
                }
                Token::Comma => {
                    if total_backticks <= 0 {
                        return Err(From::from(ParseError::new(sp, ParseErrorKind::UnbalancedComma)));
                    }
                    total_backticks -= 1;
                    if let Some(&mut Group::Backticks(ref mut n)) = stack.last_mut() {
                        *n -= 1;
                        continue;
                    }
                    stack.push(Group::Backticks(-1));
                    continue;
                }
                Token::CommaAt => {
                    if total_backticks <= 0 {
                        return Err(From::from(ParseError::new(sp, ParseErrorKind::UnbalancedComma)));
                    }
                    total_backticks -= 1;
                    stack.push(Group::CommaAt);
                    continue;
                }
                Token::Quote => {
                    if let Some(&mut Group::Quotes(ref mut n)) = stack.last_mut() {
                        *n += 1;
                        continue;
                    }
                    stack.push(Group::Quotes(1));
                    continue;
                }
                Token::End => {
                    if let Some((doc_sp, _)) = doc {
                        return Err(From::from(ParseError::new(doc_sp,
                            ParseErrorKind::DocCommentEof)));
                    }

                    let any_paren = stack.iter().any(|group| {
                        match *group {
                            Group::Parens(_, _) => true,
                            _ => false
                        }
                    });

                    if any_paren {
                        Err(From::from(ParseError::new(sp,
                            ParseErrorKind::MissingCloseParen)))
                    } else {
                        Err(From::from(ParseError::new(sp,
                            ParseErrorKind::UnexpectedEof)))
                    }
                }
            };

            if let Some((doc_sp, _)) = doc {
                return Err(From::from(ParseError::new(doc_sp,
                    ParseErrorKind::CannotDocumentItem)));
            }

            let mut v = r?;

            loop {
                match stack.last_mut() {
                    None => return Ok(v),
                    Some(&mut Group::Parens(ref mut values, _)) => {
                        values.push(v);
                        break;
                    }
                    _ => ()
                }

                let group = stack.pop().unwrap();

                match group {
                    // 0 backticks is ignored, but must still be considered
                    // a group because an expression must follow.
                    Group::Backticks(n) if n > 0 => {
                        total_backticks -= n;
                        v = v.quasiquote(n as u32);
                    }
                    Group::Backticks(n) if n < 0 => {
                        total_backticks -= n; // Subtracting a negative
                        v = v.comma((-n) as u32);
                    }
                    Group::CommaAt => {
                        total_backticks += 1;
                        v = v.comma_at(1);
                    }
                    Group::Quotes(n) => v = v.quote(n),
                    _ => ()
                }
            }
        }
    }

    /// Parses a single expression from the input stream.
    /// If any tokens remain after the expression, an error is returned.
    pub fn parse_single_expr(&mut self) -> Result<Value, Error> {
        let expr = self.parse_expr()?;

        match self.next()? {
            (_, Token::End) => Ok(expr),
            (sp, tok) => Err(From::from(ParseError::new(sp, ParseErrorKind::UnexpectedToken{
                expected: "eof",
                found: tok.name(),
            })))
        }
    }

    /// Parse a series of expressions from the input stream.
    pub fn parse_exprs(&mut self) -> Result<Vec<Value>, Error> {
        let mut res = Vec::new();

        if let Some((_, doc)) = self.read_module_doc_comment()? {
            res.push(vec![
                Value::Name(standard_names::SET_MODULE_DOC),
                format_doc_comment(doc).into(),
            ].into());
        }

        loop {
            match self.peek()? {
                (_sp, Token::End) => break,
                _ => res.push(self.parse_expr()?)
            }
        }

        Ok(res)
    }

    /// Returns a borrowed reference to the contained `Lexer`.
    pub fn lexer(&self) -> &Lexer<'lex> {
        &self.lexer
    }

    /// Returns the the next token if it is a doc comment.
    /// Otherwise, `None` is returned and no token is consumed.
    fn read_doc_comment(&mut self)
            -> Result<Option<(Span, &'lex str)>, ParseError> {
        match self.peek()? {
            (sp, Token::DocComment(doc)) => {
                self.cur_token.take();
                Ok(Some((sp, doc)))
            }
            _ => Ok(None)
        }
    }

    /// Returns the content of the next token if it is a module-level doc
    /// comment, one beginning with at least three semicolon characters.
    fn read_module_doc_comment(&mut self)
            -> Result<Option<(Span, &'lex str)>, ParseError> {
        match self.peek()? {
            (sp, Token::DocComment(doc)) if doc.starts_with(MODULE_DOC_COMMENT) => {
                self.cur_token.take();
                Ok(Some((sp, doc)))
            }
            _ => Ok(None)
        }
    }

    fn add_name(&mut self, name: &'lex str) -> Name {
        let mut names = self.ctx.scope().borrow_names_mut();
        *self.name_cache.entry(name).or_insert_with(
            || get_standard_name_for(name).unwrap_or_else(|| names.add(name)))
    }

    fn name_value(&mut self, name: &'lex str) -> Value {
        match name {
            "true" => Value::Bool(true),
            "false" => Value::Bool(false),
            _ => {
                let name = self.add_name(name);
                Value::Name(name)
            }
        }
    }

    fn next(&mut self) -> Result<(Span, Token<'lex>), ParseError> {
        let r = self.peek()?;
        self.cur_token = None;
        Ok(r)
    }

    /// Returns the next token without consuming it
    fn peek(&mut self) -> Result<(Span, Token<'lex>), ParseError> {
        if let Some(tok) = self.cur_token {
            Ok(tok)
        } else {
            let tok = self.lexer.next_token()?;
            self.cur_token = Some(tok);
            Ok(tok)
        }
    }
}

fn format_doc_comment(doc: &str) -> String {
    let mut buf = String::new();

    for line in doc.lines() {
        // Multi-line doc comments may contain "  ;; foo",
        // so we strip leading whitespace, semicolons, then one whitespace char.
        buf.push_str(trim_first(
            line.trim_left_matches(char::is_whitespace)
                .trim_left_matches(';'), char::is_whitespace));
        buf.push('\n');
    }

    buf
}

fn trim_first<F: FnOnce(char) -> bool>(s: &str, f: F) -> &str {
    let mut chars = s.chars();

    match chars.next() {
        Some(ch) if f(ch) => chars.as_str(),
        _ => s
    }
}

fn insert_doc_comment(mut items: Vec<Value>, doc: Option<(Span, &str)>)
        -> Result<Value, ParseError> {
    if let Some((sp, doc)) = doc {
        if items.len() == 3 {
            items.insert(2, format_doc_comment(doc).into());
        } else {
            return Err(ParseError::new(sp, ParseErrorKind::CannotDocumentItem));
        }
    }

    Ok(items.into())
}

fn parse_byte(s: &str) -> Result<u8, ParseError> {
    let (b, _) = string::parse_byte(s, 0)?;
    Ok(b)
}

fn parse_char(s: &str) -> Result<char, ParseError> {
    let (ch, _) = string::parse_char(s, 0)?;
    Ok(ch)
}

fn parse_bytes(s: &str) -> Result<Bytes, ParseError> {
    let (b, _) = if s.starts_with("#br") {
        string::parse_raw_byte_string(&s[2..], 0)?
    } else {
        string::parse_byte_string(&s[2..], 0)?
    };
    Ok(Bytes::new(b))
}

fn parse_path(s: &str) -> Result<PathBuf, ParseError> {
    let (s, _) = if s.starts_with("#pr") {
        string::parse_raw_string(&s[2..], 0)?
    } else {
        string::parse_string(&s[2..], 0)?
    };
    Ok(PathBuf::from(s))
}

fn parse_string(s: &str) -> Result<String, ParseError> {
    let (s, _) = if s.starts_with('r') {
        string::parse_raw_string(s, 0)?
    } else {
        string::parse_string(s, 0)?
    };
    Ok(s)
}

fn parse_float(s: &str) -> Result<f64, ParseErrorKind> {
    strip_underscores(s).parse()
        .map_err(|_| ParseErrorKind::LiteralParseError)
}

fn parse_integer(ctx: &Context, s: &str, base: u32, sp: Span)
        -> Result<Integer, Error> {
    let s = match base {
        10 => s,
        _ => &s[2..]
    };

    let s = strip_underscores(s);

    check_integer(ctx, &s, base)?;

    Integer::from_str_radix(&s, base)
        .map_err(|_| From::from(ParseError::new(sp,
            ParseErrorKind::LiteralParseError)))
}

fn parse_ratio(ctx: &Context, s: &str, sp: Span) -> Result<Ratio, Error> {
    let s = strip_underscores(s);

    check_integer(ctx, &s, 10)?;

    s.parse().map_err(|_| From::from(ParseError::new(sp,
        ParseErrorKind::LiteralParseError)))
}

fn check_integer(ctx: &Context, mut s: &str, base: u32) -> Result<(), RestrictError> {
    let limit = ctx.restrict().max_integer_size;

    if limit == usize::max_value() {
        return Ok(());
    }

    if s.starts_with('-') {
        s = &s[1..].trim_left_matches('0');
    } else {
        s = s.trim_left_matches('0');
    }

    // Approximate the number of bits that could be represented by a number of bytes.
    let n_bits = (s.len() as f32 * (base as f32).log2()).ceil() as usize;

    if n_bits > limit {
        Err(RestrictError::IntegerLimitExceeded)
    } else {
        Ok(())
    }
}

fn strip_underscores(s: &str) -> Cow<str> {
    if s.contains('_') {
        Owned(s.chars().filter(|&ch| ch != '_').collect())
    } else {
        Borrowed(s)
    }
}

#[cfg(test)]
mod test {
    use super::{ParseError, ParseErrorKind, Parser};
    use error::Error;
    use interpreter::Interpreter;
    use lexer::{Span, Lexer};
    use value::Value;

    fn parse(s: &str) -> Result<Value, ParseError> {
        let interp = Interpreter::new();

        let mut p = Parser::new(interp.context(), Lexer::new(s, 0));
        p.parse_single_expr().map_err(|e| {
            match e {
                Error::ParseError(e) => e,
                _ => panic!("parse returned error: {:?}", e)
            }
        })
    }

    #[test]
    fn test_doc_errors() {
        assert_eq!(parse(";; foo\n(const)").unwrap_err(), ParseError{
            span: Span{lo: 0, hi: 7}, kind: ParseErrorKind::CannotDocumentItem});
        assert_eq!(parse(";; foo\n(const foo)").unwrap_err(), ParseError{
            span: Span{lo: 0, hi: 7}, kind: ParseErrorKind::CannotDocumentItem});
        assert_eq!(parse(";; foo\n(const foo bar baz)").unwrap_err(), ParseError{
            span: Span{lo: 0, hi: 7}, kind: ParseErrorKind::CannotDocumentItem});
    }

    #[test]
    fn test_errors() {
        assert_eq!(parse("(foo").unwrap_err(), ParseError{
            span: Span{lo: 4, hi: 4}, kind: ParseErrorKind::MissingCloseParen});
        assert_eq!(parse("(foo ,bar)").unwrap_err(), ParseError{
            span: Span{lo: 5, hi: 6}, kind: ParseErrorKind::UnbalancedComma});
        assert_eq!(parse("`(foo ,,bar)").unwrap_err(), ParseError{
            span: Span{lo: 7, hi: 8}, kind: ParseErrorKind::UnbalancedComma});
    }

    #[test]
    fn test_lexer_position() {
        let interp = Interpreter::new();

        let mut p = Parser::new(interp.context(),
            Lexer::new("(foo 1 2 3) bar", 0));

        p.parse_expr().unwrap();

        assert_eq!(p.lexer().current_position(), 11);
    }
}
