//! Parses string tokens from input.

use std::str::CharIndices;

use lexer::{BytePos, Span};
use parser::{ParseError, ParseErrorKind};

/// Parses a character constant
pub fn parse_char(s: &str, pos: BytePos) -> Result<(char, usize), ParseError> {
    let mut r = StringReader::new(s, pos, StringType::Char);
    r.parse_char()
}

/// Parses a string constant
pub fn parse_string(s: &str, pos: BytePos) -> Result<(String, usize), ParseError> {
    let mut r = StringReader::new(s, pos, StringType::Normal);
    r.parse_string()
}

/// Parses a raw string constant
pub fn parse_raw_string(s: &str, pos: BytePos) -> Result<(String, usize), ParseError> {
    let mut r = StringReader::new(s, pos, StringType::Raw);
    r.parse_string()
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum StringType {
    Char,
    Normal,
    Raw,
}

struct StringReader<'a> {
    chars: CharIndices<'a>,
    start: BytePos,
    last_index: usize,
    end_index: usize,
    ty: StringType,
}

impl<'a> StringReader<'a> {
    fn new(input: &str, pos: BytePos, ty: StringType) -> StringReader {
        StringReader{
            chars: input.char_indices(),
            start: pos,
            last_index: 0,
            end_index: 0,
            ty: ty,
        }
    }

    fn parse_char(&mut self) -> Result<(char, usize), ParseError> {
        try!(self.expect('#', |slf, ch| ParseError::new(slf.span_one(),
            ParseErrorKind::InvalidChar(ch))));
        try!(self.expect('\'', |slf, ch| ParseError::new(slf.span_one(),
            ParseErrorKind::InvalidChar(ch))));

        let ch = match try!(self.consume_char()) {
            '\'' => return Err(ParseError::new(self.span_one(),
                ParseErrorKind::InvalidChar('\''))),
            '\\' => try!(self.parse_char_escape()),
            ch => ch
        };

        try!(self.expect('\'', |slf, _| ParseError::new(
            slf.span_from(slf.start, 1),
            ParseErrorKind::UnterminatedChar)));

        Ok((ch, self.last_index + 1))
    }

    fn parse_string(&mut self) -> Result<(String, usize), ParseError> {
        let mut res = String::new();

        let mut n_hash = 0;

        if self.ty == StringType::Raw {
            try!(self.expect('r', |slf, ch| ParseError::new(slf.span_one(),
                ParseErrorKind::InvalidChar(ch))));

            loop {
                match try!(self.consume_char()) {
                    '#' => n_hash += 1,
                    '"' => break,
                    ch => return Err(ParseError::new(self.span_one(),
                        ParseErrorKind::InvalidChar(ch)))
                }
            }
        } else {
            try!(self.expect('"', |slf, ch| ParseError::new(slf.span_one(),
                ParseErrorKind::InvalidChar(ch))));
        }

        loop {
            match try!(self.consume_char()) {
                '"' => {
                    if n_hash == 0 || try!(self.check_end(n_hash)) {
                        break;
                    } else {
                        res.push('"');
                    }
                }
                '\\' if self.ty == StringType::Normal => {
                    if let Some(ch) = try!(self.parse_string_escape()) {
                        res.push(ch);
                    }
                }
                ch => res.push(ch)
            }
        }

        Ok((res, self.last_index + 1))
    }

    fn check_end(&mut self, n_hash: usize) -> Result<bool, ParseError> {
        let save_chars = self.chars.clone();
        let save_index = self.last_index;

        for _ in 0..n_hash {
            if try!(self.consume_char()) != '#' {
                self.chars = save_chars;
                self.last_index = save_index;
                return Ok(false);
            }
        }

        Ok(true)
    }

    fn consume_char(&mut self) -> Result<char, ParseError> {
        match self.chars.next() {
            Some((ind, '\r')) => {
                self.last_index = ind;
                self.end_index = ind + 1;

                match self.chars.next() {
                    Some((ind, '\n')) => {
                        self.last_index = ind;
                        self.end_index = ind + 1;
                        Ok('\n')
                    }
                    _ => Err(ParseError::new(
                        self.span_from(ind as BytePos, 1),
                        ParseErrorKind::InvalidChar('\r')))
                }
            }
            Some((ind, ch)) => {
                self.last_index = ind;
                self.end_index = ind + ch.len_utf8();
                Ok(ch)
            }
            None => Err(ParseError::new(self.span_from(self.start, 1),
                if self.ty == StringType::Char {
                    ParseErrorKind::UnterminatedChar
                } else {
                    ParseErrorKind::UnterminatedString
                }))
        }
    }

    fn expect<F>(&mut self, ch: char, f: F) -> Result<(), ParseError>
            where F: FnOnce(&Self, char) -> ParseError {
        let c = try!(self.consume_char());
        if c == ch {
            Ok(())
        } else {
            Err(f(self, c))
        }
    }

    fn parse_char_escape(&mut self) -> Result<char, ParseError> {
        match try!(self.consume_char()) {
            '\\' => Ok('\\'),
            '\'' => Ok('\''),
            '"' => Ok('"'),
            '0' => Ok('\0'),
            'n' => Ok('\n'),
            'r' => Ok('\r'),
            't' => Ok('\t'),
            'u' => self.parse_unicode(),
            'x' => self.parse_byte(),
            ch => Err(ParseError::new(self.span_one(),
                ParseErrorKind::UnknownCharEscape(ch)))
        }
    }

    fn parse_string_escape(&mut self) -> Result<Option<char>, ParseError> {
        match try!(self.peek_char()) {
            '\r' | '\n' => {
                try!(self.consume_char());
                loop {
                    match try!(self.peek_char()) {
                        ' ' | '\t' => { try!(self.consume_char()); },
                        _ => break
                    }
                }
                Ok(None)
            }
            _ => self.parse_char_escape().map(Some)
        }
    }

    fn parse_byte(&mut self) -> Result<char, ParseError> {
        let a = match try!(self.consume_char()) {
            ch if !ch.is_digit(16) => return Err(ParseError::new(
                self.span_one(), ParseErrorKind::InvalidNumericEscape('x'))),
            ch => ch
        };
        let b = match try!(self.consume_char()) {
            ch if !ch.is_digit(16) => return Err(ParseError::new(
                self.span_one(), ParseErrorKind::InvalidNumericEscape('x'))),
            ch => ch
        };

        if a > '7' {
            return Err(ParseError::new(self.back_span(1, 2),
                ParseErrorKind::InvalidNumericEscape('x')));
        }

        Ok(::std::char::from_u32(
            (a.to_digit(16).unwrap() << 4) | b.to_digit(16).unwrap()).unwrap())
    }

    fn parse_unicode(&mut self) -> Result<char, ParseError> {
        try!(self.expect('{', |slf, _| ParseError::new(slf.span_one(),
            ParseErrorKind::InvalidNumericEscape('u'))));

        let mut n_digits = 0;
        let mut total = 0;

        loop {
            match try!(self.consume_char()) {
                '}' if n_digits != 0 => break,
                ch if ch.is_digit(16) => {
                    if n_digits == 6 {
                        return Err(ParseError::new(self.span_one(),
                            ParseErrorKind::InvalidNumericEscape(ch)));
                    }
                    n_digits += 1;
                    total = (total << 4) | ch.to_digit(16).unwrap();
                }
                ch => return Err(ParseError::new(
                    self.span_one(), ParseErrorKind::InvalidNumericEscape(ch))),
            }
        }

        ::std::char::from_u32(total)
            .ok_or_else(|| ParseError::new(
                self.back_span(n_digits + 1, n_digits),
                ParseErrorKind::InvalidNumericEscape('u')))
    }

    fn peek_char(&mut self) -> Result<char, ParseError> {
        match self.chars.clone().next() {
            Some((_, ch)) => Ok(ch),
            None => Err(ParseError::new(self.span_from(self.start, 1),
                if self.ty == StringType::Char {
                    ParseErrorKind::UnterminatedChar
                } else {
                    ParseErrorKind::UnterminatedString
                }))
        }
    }

    fn back_span(&self, back: BytePos, len: BytePos) -> Span {
        let start = self.start + self.last_index as BytePos - back;
        Span{lo: start, hi: start + len}
    }

    fn span_one(&self) -> Span {
        Span{lo: self.last_index as BytePos, hi: self.end_index as BytePos}
    }

    fn span_from(&self, start: BytePos, len: BytePos) -> Span {
        Span{lo: start, hi: start + len}
    }
}

#[cfg(test)]
mod test {
    use parser::ParseError;
    use super::{StringReader, StringType};

    fn parse_char(s: &str) -> Result<char, ParseError> {
        let mut r = StringReader::new(s, 0, StringType::Char);
        r.parse_char().map(|r| r.0)
    }

    fn parse_string(s: &str, ty: StringType) -> Result<String, ParseError> {
        let mut r = StringReader::new(s, 0, ty);
        r.parse_string().map(|r| r.0)
    }

    #[test]
    fn test_parse_string() {
        let n = StringType::Normal;
        let r = StringType::Raw;

        assert_eq!(parse_char(r"#'a'").unwrap(), 'a');
        assert_eq!(parse_char(r"#'\''").unwrap(), '\'');
        assert_eq!(parse_char(r"#'\x7f'").unwrap(), '\x7f');
        assert_eq!(parse_char(r"#'\u{1234}'").unwrap(), '\u{1234}');

        assert_eq!(parse_string(r#""foo""#, n).unwrap(), "foo");
        assert_eq!(parse_string(r#"r"foo""#, r).unwrap(), "foo");
        assert_eq!(parse_string(r##"r#""foo""#"##, r).unwrap(), r#""foo""#);
    }
}
