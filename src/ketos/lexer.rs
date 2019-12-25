//! Produces tokens from an input stream.

use std::iter::{once, repeat};
use std::str::CharIndices;

use crate::parser::{ParseError, ParseErrorKind};
use crate::string;

/// Represents a single unit of code input.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Token<'lex> {
    /// Left parenthesis `(`
    LeftParen,
    /// Right parenthesis `)`
    RightParen,
    /// A series of line comments beginning with `;;`,
    /// used to document declared values.
    DocComment(&'lex str),
    /// Floating point literal
    Float(&'lex str),
    /// Integer literal in a given radix
    Integer(&'lex str, u32),
    /// Ratio literal
    Ratio(&'lex str),
    /// Character literal
    Char(&'lex str),
    /// String literal
    String(&'lex str),
    /// Byte literal
    Byte(&'lex str),
    /// Byte string literal
    Bytes(&'lex str),
    /// Path literal
    Path(&'lex str),
    /// Identifier name
    Name(&'lex str),
    /// Identifier keyword
    Keyword(&'lex str),
    /// Backtick quote `` ` ``
    BackQuote,
    /// Comma `,`
    Comma,
    /// Comma followed by at `,@`
    CommaAt,
    /// Single-quote `'`
    Quote,
    /// End of input stream
    End,
}

impl<'lex> Token<'lex> {
    /// Returns a human-readable name of a token.
    pub fn name(&self) -> &'static str {
        match *self {
            Token::LeftParen => "(",
            Token::RightParen => ")",
            Token::DocComment(_) => "doc-comment",
            Token::Float(_) => "float",
            Token::Integer(_, _) => "integer",
            Token::Ratio(_) => "ratio",
            Token::Name(_) => "name",
            Token::Char(_) => "char",
            Token::String(_) => "string",
            Token::Byte(_) => "byte",
            Token::Bytes(_) => "bytes",
            Token::Path(_) => "path",
            Token::Keyword(_) => "keyword",
            Token::BackQuote => "`",
            Token::Comma => ",",
            Token::CommaAt => ",@",
            Token::Quote => "'",
            Token::End => "end-of-file",
        }
    }
}

/// Represents a byte position within an input stream.
pub type BytePos = u32;

/// Produced by `highlight_span` to help in printing a line of code with
/// a span highlighted.
#[derive(Clone, Debug)]
pub struct SpanDisplay<'a> {
    /// Filename
    pub filename: Option<&'a str>,
    /// Line number
    pub line: usize,
    /// Column offset
    pub col: usize,
    /// Line of source code
    pub source: &'a str,
    /// Highlighting string
    pub highlight: String,
}

/// Returns a structure which helps in highlighting a span within a body of text.
///
/// # Panics
///
/// Panics if `span` is not valid.
pub fn highlight_span(text: &str, span: Span) -> SpanDisplay {
    let line_start = match text[..span.lo as usize].rfind('\n') {
        Some(pos) => pos + 1,
        None => 0
    };

    let line_end = match text[line_start..].find('\n') {
        Some(pos) => line_start + pos,
        None => text.len()
    };

    let pre_chars = text[line_start..span.lo as usize].chars().count();
    let span_str = &text[span.lo as usize..span.hi as usize];

    // If the span spans multiple lines, just highlight to the end of the line.
    let span_chars = match span_str.find('\n') {
        Some(pos) => span_str[..pos].chars().count(),
        None => span_str.chars().count()
    };

    let line_no = text[..line_start].chars()
        .filter(|&ch| ch == '\n').count() + 1;

    SpanDisplay{
        filename: None,
        line: line_no,
        col: pre_chars,
        source: &text[line_start..line_end],
        highlight: repeat(' ').take(pre_chars)
            .chain(once('^'))
            .chain(repeat('~').take(span_chars.saturating_sub(1))).collect(),
    }
}

/// Contains source code of parsed programs
#[derive(Clone, Debug)]
pub struct CodeMap {
    text: String,
    files: Vec<File>,
}

#[derive(Clone, Debug)]
struct File {
    path: Option<String>,
    begin: BytePos,
}

impl CodeMap {
    /// Creates a new `CodeMap`.
    pub fn new() -> CodeMap {
        CodeMap{
            text: String::new(),
            files: Vec::new(),
        }
    }

    /// Adds a source to the codemap, returning its offset in the internal buffer.
    pub fn add_source(&mut self, text: &str, path: Option<String>) -> BytePos {
        let begin = self.text.len() as BytePos;

        self.text.push_str(text);
        self.files.push(File{ path, begin });

        begin
    }

    /// Clears all source from the codemap.
    pub fn clear(&mut self) {
        self.text.clear();
        self.files.clear();
    }

    /// Highlights a span within the codemap.
    ///
    /// # Panics
    ///
    /// Panics if `span` is not valid.
    pub fn highlight_span(&self, span: Span) -> SpanDisplay {
        let n = match self.files.binary_search_by(|f| f.begin.cmp(&span.lo)) {
            Ok(n) => n,
            Err(n) => n - 1
        };

        let end = match self.files.get(n as usize + 1) {
            Some(f) => f.begin,
            None => self.text.len() as BytePos
        };

        if span.hi > end {
            panic!("span {:?} spans multiple files", span);
        }

        let f = &self.files[n as usize];

        let Span{lo, hi} = span;
        let adj_span = Span{lo: lo - f.begin, hi: hi - f.begin};

        SpanDisplay{
            filename: f.path.as_ref().map(|s| &s[..]),
            ..highlight_span(&self.text[f.begin as usize..end as usize], adj_span)
        }
    }
}

/// Produces `Token`s from an input string.
pub struct Lexer<'lex> {
    input: &'lex str,
    cur_pos: BytePos,
    code_offset: BytePos,
}

/// Represents a beginning and end point within a body of text.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Span {
    /// First byte of range
    pub lo: BytePos,
    /// One byte past the end of range
    pub hi: BytePos,
}

impl Span {
    /// Returns an empty `Span` at the given offset.
    pub fn empty(pos: BytePos) -> Span {
        Span{lo: pos, hi: pos}
    }

    /// Returns a `Span` spanning a single char.
    pub fn one(pos: BytePos, ch: char) -> Span {
        Span{lo: pos, hi: pos + ch.len_utf8() as BytePos}
    }

    /// Returns a `Span` spanning a single byte.
    pub fn byte(pos: BytePos) -> Span {
        Span{lo: pos, hi: pos + 1}
    }
}

impl<'lex> Lexer<'lex> {
    /// Creates a new `Lexer` to read tokens from the input string.
    pub fn new(input: &str, offset: BytePos) -> Lexer {
        Lexer{
            input,
            cur_pos: 0,
            code_offset: offset,
        }
    }

    /// Scans the input stream for the next token, returning the token and
    /// the span of input text from which it was scanned.
    pub fn next_token(&mut self) -> Result<(Span, Token<'lex>), ParseError> {
        let mut chars = self.input.char_indices();

        while let Some((ind, ch)) = chars.next() {
            let lo = self.cur_pos;

            let res = match ch {
                '(' => Ok((Token::LeftParen, 1)),
                ')' => Ok((Token::RightParen, 1)),
                '\'' => Ok((Token::Quote, 1)),
                '`' => Ok((Token::BackQuote, 1)),
                ',' => match chars.next() {
                    Some((_, '@')) => Ok((Token::CommaAt, 2)),
                    _ => Ok((Token::Comma, 1)),
                },
                '-' | '0' ..= '9' => parse_number(&self.input[ind..]),
                '"' => Ok(parse_string(&self.input[ind..], self.code_offset + lo)?),
                '#' => match chars.next() {
                    Some((_, 'b')) => {
                        match chars.next() {
                            Some((_, 'r')) => Ok(parse_raw_bytes(&self.input[ind..],
                                self.code_offset + lo)?),
                            Some((_, '"')) => Ok(parse_bytes(&self.input[ind..],
                                self.code_offset + lo)?),
                            Some((_, '\'')) => Ok(parse_byte(&self.input[ind..],
                                self.code_offset + lo)?),
                            _ => Err(ParseErrorKind::InvalidToken)
                        }
                    }
                    Some((_, 'p')) => {
                        match chars.next() {
                            Some((_, 'r')) => Ok(parse_raw_path(&self.input[ind..],
                                self.code_offset + lo)?),
                            Some((_, '"')) => Ok(parse_path(&self.input[ind..],
                                self.code_offset + lo)?),
                            _ => Err(ParseErrorKind::InvalidToken)
                        }
                    }
                    Some((_, '\'')) => Ok(parse_char(&self.input[ind..],
                        self.code_offset + lo)?),
                    Some((_, '|')) => match consume_block_comment(ind, &mut chars) {
                        Ok(n) => {
                            self.cur_pos += n as BytePos;
                            continue;
                        }
                        Err(k) => Err(k)
                    },
                    Some(_) => Err(ParseErrorKind::InvalidToken),
                    None => Err(ParseErrorKind::UnexpectedEof)
                },
                'r' => match chars.next() {
                    Some((_, '"')) | Some((_, '#')) =>
                        Ok(parse_raw_string(&self.input[ind..],
                            self.code_offset + lo)?),
                    _ => parse_name(&self.input[ind..])
                },
                ':' => parse_keyword(&self.input[ind..]),
                ';' => {
                    match chars.clone().next() {
                        Some((_, ';')) => Ok(parse_doc_comment(&self.input[ind..])),
                        _ => {
                            self.cur_pos += consume_line_comment(ind, &mut chars) as BytePos;
                            continue;
                        }
                    }
                }
                '\r' => match chars.next() {
                    Some((_, '\n')) => {
                        self.cur_pos += 2;
                        continue;
                    }
                    _ => Err(ParseErrorKind::InvalidChar('\r'))
                },
                ch if ch.is_whitespace() => {
                    self.cur_pos += ch.len_utf8() as BytePos;
                    continue;
                }
                _ if is_identifier(ch) => parse_name(&self.input[ind..]),
                ch => Err(ParseErrorKind::InvalidChar(ch))
            };

            let (tok, size) = match res {
                Ok(v) => v,
                Err(kind) => return Err(ParseError::new(
                    self.span(Span::one(lo, ch)), kind))
            };

            self.cur_pos += size as BytePos;
            self.input = &self.input[ind + size..];

            let sp = Span{lo, hi: lo + size as BytePos};

            return Ok((self.span(sp), tok));
        }

        self.input = &self.input[..0];
        Ok((self.span(Span::empty(self.cur_pos)), Token::End))
    }

    /// Skips over a shebang line at the start of input. This is used when
    /// parsing files which, on Unix systems, may use a line consisting of `#!`
    /// followed by a path to the interpreter.
    ///
    /// # Panics
    ///
    /// Panics if any tokens have already been scanned from the input stream.
    pub fn skip_shebang(&mut self) {
        if self.cur_pos != 0 {
            panic!("skip_shebang called after next_token");
        }

        if self.input.starts_with("#!") {
            let pos = match self.input.find('\n') {
                Some(pos) => pos,
                None => self.input.len()
            };
            self.input = &self.input[pos..];
            self.cur_pos = pos as BytePos;
        }
    }

    /// Returns the current position within the input string.
    ///
    /// The next call to `next_token` will begin searching at this point.
    pub fn current_position(&self) -> BytePos {
        self.cur_pos
    }

    fn span(&self, span: Span) -> Span {
        let Span{lo, hi} = span;
        Span{lo: self.code_offset + lo, hi: self.code_offset + hi}
    }
}

fn consume_block_comment(start: usize, chars: &mut CharIndices) -> Result<usize, ParseErrorKind> {
    let mut n_blocks = 1;

    loop {
        match chars.next() {
            Some((_, '|')) => match chars.clone().next() {
                Some((ind, '#')) => {
                    chars.next();
                    n_blocks -= 1;
                    if n_blocks == 0 {
                        return Ok(ind - start + 1);
                    }
                }
                Some(_) => (),
                None => break
            },
            Some((_, '#')) => match chars.clone().next() {
                Some((_, '|')) => {
                    chars.next();
                    n_blocks += 1;
                }
                Some(_) => (),
                None => break
            },
            Some((ind, ';')) => {
                consume_line_comment(ind, chars);
            }
            Some(_) => (),
            None => break
        }
    }

    Err(ParseErrorKind::UnterminatedComment)
}

fn consume_line_comment(start: usize, chars: &mut CharIndices) -> usize {
    let mut last = start;

    for (ind, ch) in chars {
        last = ind;
        if ch == '\n' {
            break;
        }
    }

    last - start + 1
}

fn parse_doc_comment(input: &str) -> (Token, usize) {
    let mut chars = input.char_indices();
    let mut begin_line = true;
    let mut end = 0;

    loop {
        match chars.next() {
            Some((_, ';')) if begin_line => {
                match chars.next() {
                    Some((_, ';')) => {
                        begin_line = false;
                    }
                    _ => break
                }
            }
            Some((_, ch)) if begin_line &&
                ch != '\r' && ch != '\n' &&
                ch.is_whitespace() => (),
            _ if begin_line => break,
            Some((_, '\r')) => {
                if let Some((ind, '\n')) = chars.next() {
                    end = ind + 1;
                    begin_line = true;
                }
            }
            Some((ind, '\n')) => {
                end = ind + 1;
                begin_line = true;
            }
            Some(_) => (),
            None => {
                end = input.len();
                break;
            }
        }
    }

    (Token::DocComment(&input[..end]), end)
}

fn is_identifier(ch: char) -> bool {
    match ch {
        '!' | '$' | '%' | '&' | '*' | '+' | '-' | '.' | '/' |
        '<' | '=' | '>' | '?' | '^' | '_' | '|' => true,
        _ if ch.is_alphanumeric() => true,
        _ => false
    }
}

fn parse_identifier(input: &str) -> Result<(&str, usize), ParseErrorKind> {
    for (ind, ch) in input.char_indices() {
        if !is_identifier(ch) {
            return Ok((&input[..ind], ind));
        }
    }

    Ok((input, input.len()))
}

fn parse_keyword(input: &str) -> Result<(Token, usize), ParseErrorKind> {
    parse_identifier(&input[1..]) // Skip leading ':'
        .and_then(|(ident, size)| {
            if size == 0 {
                Err(ParseErrorKind::InvalidToken)
            } else {
                Ok((Token::Keyword(ident), size + 1))
            }
        })
}

fn parse_name(input: &str) -> Result<(Token, usize), ParseErrorKind> {
    parse_identifier(input).map(|(ident, size)| (Token::Name(ident), size))
}

fn parse_number(input: &str) -> Result<(Token, usize), ParseErrorKind> {
    let mut digits = false;
    let mut dot = false;
    let mut exp = false;
    let mut exp_digit = false;
    let mut slash = false;
    let mut slash_digit = false;
    let mut size = input.len();

    let (base, prefix_offset, rest) = if input.starts_with("0x") {
        (16, 2, &input[2..])
    } else if input.starts_with("0o") {
        (8, 2, &input[2..])
    } else if input.starts_with("0b") {
        (2, 2, &input[2..])
    } else if input.starts_with('-') {
        match input[1..].chars().next() {
            Some(ch) if ch.is_digit(10) => (10, 1, &input[1..]),
            // Actually a name beginning with '-' rather a number
            _ => return parse_name(input)
        }
    } else {
        (10, 0, input)
    };

    for (ind, ch) in rest.char_indices() {
        match ch {
            _ if ch.is_digit(base) => {
                digits = true;

                if exp {
                    exp_digit = true;
                } else if slash {
                    slash_digit = true;
                }
            }
            '+' | '-' => {
                if exp_digit || !exp {
                    return Err(ParseErrorKind::InvalidLiteral);
                }
                exp_digit = true;
            }
            '.' => {
                if dot || slash || base != 10 {
                    return Err(ParseErrorKind::InvalidLiteral);
                }
                dot = true;
            }
            'e' | 'E' => {
                if exp || slash || base != 10 {
                    return Err(ParseErrorKind::InvalidLiteral);
                }
                dot = true;
                exp = true;
            }
            '/' => {
                if dot || exp || slash || base != 10 {
                    return Err(ParseErrorKind::InvalidLiteral);
                }
                slash = true;
            }
            '_' => (),
            _ if !is_identifier(ch) => {
                size = prefix_offset + ind;
                break;
            }
            _ => return Err(ParseErrorKind::InvalidLiteral)
        }
    }

    if !digits {
        Err(ParseErrorKind::InvalidLiteral)
    } else if dot || exp {
        Ok((Token::Float(&input[..size]), size))
    } else if slash {
        if !slash_digit {
            Err(ParseErrorKind::InvalidLiteral)
        } else {
            Ok((Token::Ratio(&input[..size]), size))
        }
    } else {
        Ok((Token::Integer(&input[..size], base), size))
    }
}

fn parse_byte(input: &str, pos: BytePos) -> Result<(Token, usize), ParseError> {
    let (_, size) = string::parse_byte(input, pos)?;
    Ok((Token::Byte(&input[..size]), size))
}

fn parse_bytes(input: &str, pos: BytePos) -> Result<(Token, usize), ParseError> {
    let (_, size) = string::parse_byte_string(&input[2..], pos + 2)?;
    Ok((Token::Bytes(&input[..size + 2]), size + 2))
}

fn parse_raw_bytes(input: &str, pos: BytePos) -> Result<(Token, usize), ParseError> {
    let (_, size) = string::parse_raw_byte_string(&input[2..], pos + 2)?;
    Ok((Token::Bytes(&input[..size + 2]), size + 2))
}

fn parse_path(input: &str, pos: BytePos) -> Result<(Token, usize), ParseError> {
    let (_, size) = string::parse_string(&input[2..], pos + 2)?;
    Ok((Token::Path(&input[..size + 2]), size + 2))
}

fn parse_raw_path(input: &str, pos: BytePos) -> Result<(Token, usize), ParseError> {
    let (_, size) = string::parse_raw_string(&input[2..], pos + 2)?;
    Ok((Token::Path(&input[..size + 2]), size + 2))
}

fn parse_char(input: &str, pos: BytePos) -> Result<(Token, usize), ParseError> {
    let (_, size) = string::parse_char(input, pos)?;
    Ok((Token::Char(&input[..size]), size))
}

fn parse_string(input: &str, pos: BytePos) -> Result<(Token, usize), ParseError> {
    let (_, size) = string::parse_string(input, pos)?;
    Ok((Token::String(&input[..size]), size))
}

fn parse_raw_string(input: &str, pos: BytePos) -> Result<(Token, usize), ParseError> {
    let (_, size) = string::parse_raw_string(input, pos)?;
    Ok((Token::String(&input[..size]), size))
}

#[cfg(test)]
mod test {
    use super::{BytePos, Lexer, Span, Token};
    use crate::parser::ParseErrorKind;

    fn sp(lo: BytePos, hi: BytePos) -> Span {
        Span{lo, hi}
    }

    fn tokens(s: &str) -> Vec<(Span, Token)> {
        let mut lex = Lexer::new(s, 0);
        let mut res = Vec::new();

        loop {
            match lex.next_token().unwrap() {
                (_, Token::End) => break,
                tok => res.push(tok),
            }
        }

        res
    }

    fn error(s: &str) -> Result<(), ParseErrorKind> {
        let mut lex = Lexer::new(s, 0);
        lex.next_token().map(|_| ()).map_err(|e| e.kind)
    }

    #[test]
    fn test_comment() {
        assert_eq!(tokens("1\n;foo\n2"),
            [(sp(0, 1), Token::Integer("1", 10)),
             (sp(7, 8), Token::Integer("2", 10))]);

        assert_eq!(tokens("1 #| lol |# 2"),
            [(sp(0, 1), Token::Integer("1", 10)),
             (sp(12, 13), Token::Integer("2", 10))]);

        assert_eq!(tokens("1 #| lol\n; wut |#\n nou |# 2"),
            [(sp(0, 1), Token::Integer("1", 10)),
             (sp(26, 27), Token::Integer("2", 10))]);

        assert_eq!(tokens("1 #| lol #| wut |# #| nou |# lolk |# 2"),
            [(sp(0, 1), Token::Integer("1", 10)),
             (sp(37, 38), Token::Integer("2", 10))]);
    }

    #[test]
    fn test_lexer() {
        assert_eq!(tokens("1 2 3"),
            [(sp(0, 1), Token::Integer("1", 10)),
             (sp(2, 3), Token::Integer("2", 10)),
             (sp(4, 5), Token::Integer("3", 10))]);

        assert_eq!(tokens("1 foo 3"),
            [(sp(0, 1), Token::Integer("1", 10)),
             (sp(2, 5), Token::Name("foo")),
             (sp(6, 7), Token::Integer("3", 10))]);

        assert_eq!(tokens("0b0101 0o777 0xdeadBEEF"),
            [(sp(0, 6), Token::Integer("0b0101", 2)),
             (sp(7, 12), Token::Integer("0o777", 8)),
             (sp(13, 23), Token::Integer("0xdeadBEEF", 16))]);

        assert_eq!(tokens("1/2 -10/3"),
            [(sp(0, 3), Token::Ratio("1/2")),
             (sp(4, 9), Token::Ratio("-10/3"))]);

        assert_eq!(tokens("-1 2.0 3e100 -4.1e-2 5e+1"),
            [(sp(0, 2), Token::Integer("-1", 10)),
             (sp(3, 6), Token::Float("2.0")),
             (sp(7, 12), Token::Float("3e100")),
             (sp(13, 20), Token::Float("-4.1e-2")),
             (sp(21, 25), Token::Float("5e+1"))]);

        assert_eq!(tokens(r"#'a' #'\'' #'\x7f' #'\u{1234}'"),
            [(sp(0, 4), Token::Char("#'a'")),
             (sp(5, 10), Token::Char(r"#'\''")),
             (sp(11, 18), Token::Char(r"#'\x7f'")),
             (sp(19, 30), Token::Char(r"#'\u{1234}'"))]);

        assert_eq!(tokens(r"#b'a' #b'\'' #b'\xff'"),
            [(sp(0, 5), Token::Byte("#b'a'")),
             (sp(6, 12), Token::Byte(r"#b'\''")),
             (sp(13, 21), Token::Byte(r"#b'\xff'"))]);

        assert_eq!(tokens(r#"#b"foo" #b"bar\xff""#),
            [(sp(0, 7), Token::Bytes(r#"#b"foo""#)),
             (sp(8, 19), Token::Bytes(r#"#b"bar\xff""#))]);

        assert_eq!(tokens(r#"#p"foo" #p"bar""#),
            [(sp(0, 7), Token::Path(r#"#p"foo""#)),
             (sp(8, 15), Token::Path(r#"#p"bar""#))]);

        assert_eq!(tokens(r##"#pr"foo\" #pr#"bar"#"##),
            [(sp(0, 9), Token::Path(r#"#pr"foo\""#)),
             (sp(10, 20), Token::Path(r##"#pr#"bar"#"##))]);

        assert_eq!(tokens(r###""a" r"\" r#"b"# r##"c"## "\x7f" "\u{1234}""###),
            [(sp(0, 3), Token::String(r#""a""#)),
             (sp(4, 8), Token::String(r#"r"\""#)),
             (sp(9, 15), Token::String(r##"r#"b"#"##)),
             (sp(16, 24), Token::String(r###"r##"c"##"###)),
             (sp(25, 31), Token::String(r#""\x7f""#)),
             (sp(32, 42), Token::String(r#""\u{1234}""#))]);

        assert_eq!(tokens("foo"), [(sp(0, 3), Token::Name("foo"))]);

        assert_eq!(tokens("()"), [
            (sp(0, 1), Token::LeftParen), (sp(1, 2), Token::RightParen)]);

        assert_eq!(tokens("(foo)"),
            [(sp(0, 1), Token::LeftParen),
             (sp(1, 4), Token::Name("foo")),
             (sp(4, 5), Token::RightParen)]);

        assert_eq!(tokens("(foo bar baz)"),
            [(sp(0, 1), Token::LeftParen),
                (sp(1, 4), Token::Name("foo")),
                (sp(5, 8), Token::Name("bar")),
                (sp(9, 12), Token::Name("baz")),
            (sp(12, 13), Token::RightParen)]);

        assert_eq!(tokens("(foo\nbar\nbaz)"),
            [(sp(0, 1), Token::LeftParen),
                (sp(1, 4), Token::Name("foo")),
                (sp(5, 8), Token::Name("bar")),
                (sp(9, 12), Token::Name("baz")),
            (sp(12, 13), Token::RightParen)]);

        assert_eq!(tokens("(foo\r\nbar\r\nbaz)"),
            [(sp(0, 1), Token::LeftParen),
                (sp(1, 4), Token::Name("foo")),
                (sp(6, 9), Token::Name("bar")),
                (sp(11, 14), Token::Name("baz")),
            (sp(14, 15), Token::RightParen)]);

        assert_eq!(tokens("(- 1)"),
            [(sp(0, 1), Token::LeftParen),
                (sp(1, 2), Token::Name("-")),
                (sp(3, 4), Token::Integer("1", 10)),
            (sp(4, 5), Token::RightParen)]);

        assert_eq!(tokens("(foo (bar baz) (spam eggs))"),
            [(sp(0, 1), Token::LeftParen),
                (sp(1, 4), Token::Name("foo")),
                (sp(5, 6), Token::LeftParen),
                    (sp(6, 9), Token::Name("bar")),
                    (sp(10, 13), Token::Name("baz")),
                (sp(13, 14), Token::RightParen),
                (sp(15, 16), Token::LeftParen),
                    (sp(16, 20), Token::Name("spam")),
                    (sp(21, 25), Token::Name("eggs")),
                (sp(25, 26), Token::RightParen),
            (sp(26, 27), Token::RightParen)]);

        assert_eq!(tokens("(foo '(bar baz))"),
            [(sp(0, 1), Token::LeftParen),
                (sp(1, 4), Token::Name("foo")),
                (sp(5, 6), Token::Quote),
                (sp(6, 7), Token::LeftParen),
                    (sp(7, 10), Token::Name("bar")),
                    (sp(11, 14), Token::Name("baz")),
                (sp(14, 15), Token::RightParen),
            (sp(15, 16), Token::RightParen)]);

        assert_eq!(tokens("(+ 1 2)"),
            [(sp(0, 1), Token::LeftParen),
                (sp(1, 2), Token::Name("+")),
                (sp(3, 4), Token::Integer("1", 10)),
                (sp(5, 6), Token::Integer("2", 10)),
            (sp(6, 7), Token::RightParen)]);

        assert_eq!(tokens("(* 1 2 (+ 3 4))"),
            [(sp(0, 1), Token::LeftParen),
                (sp(1, 2), Token::Name("*")),
                (sp(3, 4), Token::Integer("1", 10)),
                (sp(5, 6), Token::Integer("2", 10)),
                (sp(7, 8), Token::LeftParen),
                    (sp(8, 9), Token::Name("+")),
                    (sp(10, 11), Token::Integer("3", 10)),
                    (sp(12, 13), Token::Integer("4", 10)),
                (sp(13, 14), Token::RightParen),
            (sp(14, 15), Token::RightParen)]);

        assert_eq!(tokens("foo ; bar\nbaz"),
            [(sp(0, 3), Token::Name("foo")),
             (sp(10, 13), Token::Name("baz"))]);

        assert_eq!(tokens("foo; bar\nbaz"),
            [(sp(0, 3), Token::Name("foo")),
             (sp(9, 12), Token::Name("baz"))]);

        assert_eq!(tokens(";; foo"),
            [(sp(0, 6), Token::DocComment(";; foo"))]);

        assert_eq!(tokens(";; foo\n"),
            [(sp(0, 7), Token::DocComment(";; foo\n"))]);

        assert_eq!(tokens(";; foo\nbar"),
            [(sp(0, 7), Token::DocComment(";; foo\n")),
             (sp(7, 10), Token::Name("bar"))]);

        assert_eq!(tokens(";; foo\n; bar\n"),
            [(sp(0, 7), Token::DocComment(";; foo\n"))]);

        assert_eq!(tokens("; foo\n;; bar\n"),
            [(sp(6, 13), Token::DocComment(";; bar\n"))]);

        assert_eq!(tokens(";; foo\n;;\n;; bar\n"),
            [(sp(0, 17), Token::DocComment(";; foo\n;;\n;; bar\n"))]);

        assert_eq!(tokens(";; foo\n;; bar\n"),
            [(sp(0, 14), Token::DocComment(";; foo\n;; bar\n"))]);

        assert_eq!(tokens(";; foo\n\n;; bar\n"),
            [(sp(0, 7), Token::DocComment(";; foo\n")),
             (sp(8, 15), Token::DocComment(";; bar\n"))]);
    }

    #[test]
    fn test_errors() {
        assert_eq!(error("\rfoo"), Err(ParseErrorKind::InvalidChar('\r')));
        assert_eq!(error(":"), Err(ParseErrorKind::InvalidToken));

        assert_eq!(error("-0x1"), Err(ParseErrorKind::InvalidLiteral));
        assert_eq!(error("0o78"), Err(ParseErrorKind::InvalidLiteral));
        assert_eq!(error("0b012"), Err(ParseErrorKind::InvalidLiteral));
        assert_eq!(error("1e2.0"), Err(ParseErrorKind::InvalidLiteral));
        assert_eq!(error("1e2-0"), Err(ParseErrorKind::InvalidLiteral));
        assert_eq!(error("-1/-2"), Err(ParseErrorKind::InvalidLiteral));
        assert_eq!(error("0x10/2"), Err(ParseErrorKind::InvalidLiteral));
        assert_eq!(error("10e1/2"), Err(ParseErrorKind::InvalidLiteral));
        assert_eq!(error("10/2e3"), Err(ParseErrorKind::InvalidLiteral));

        assert_eq!(error("1/"), Err(ParseErrorKind::InvalidLiteral));
        assert_eq!(error("0b_"), Err(ParseErrorKind::InvalidLiteral));
        assert_eq!(error("0o_"), Err(ParseErrorKind::InvalidLiteral));
        assert_eq!(error("0x_"), Err(ParseErrorKind::InvalidLiteral));

        assert_eq!(error("#p"), Err(ParseErrorKind::InvalidToken));
        assert_eq!(error("#p x"), Err(ParseErrorKind::InvalidToken));
        assert_eq!(error("#px"), Err(ParseErrorKind::InvalidToken));
        assert_eq!(error("#pxyz"), Err(ParseErrorKind::InvalidToken));
    }

    #[test]
    fn test_position() {
        let mut l = Lexer::new("foo bar baz ", 0);

        assert_matches!(l.next_token().unwrap(), (_, Token::Name("foo")));
        assert_eq!(l.current_position(), 3);

        assert_matches!(l.next_token().unwrap(), (_, Token::Name("bar")));
        assert_eq!(l.current_position(), 7);

        assert_matches!(l.next_token().unwrap(), (_, Token::Name("baz")));
        assert_eq!(l.current_position(), 11);

        assert_matches!(l.next_token().unwrap(), (_, Token::End));
        assert_eq!(l.current_position(), 12);
    }
}
