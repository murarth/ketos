//! Implements string formatting syntax.

use std::borrow::Cow::{self, Borrowed, Owned};
use std::cmp::max;
use std::f64;
use std::fmt;
use std::iter::repeat;
use std::str::CharIndices;

use num::ToPrimitive;

use crate::exec::ExecError;
use crate::integer::Integer;
use crate::lexer::{BytePos, Span};
use crate::name::{debug_names, display_names, NameStore};
use crate::pretty::pretty_print;
use crate::value::Value;

/// Represents an error in formatting a string.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FormatError {
    /// Error message
    Error(Box<str>),
    /// Extraneous fields to directive
    ExtraFields,
    /// Field value exceeded expected range
    FieldOverflow,
    /// Wrong type to field value
    FieldTypeError{
        /// Type of value expected
        expected: &'static str,
        /// Type found
        found: &'static str,
    },
    /// End of format string reached before directive completed
    IncompleteDirective,
    /// Group-closing directive encountered without matching opener
    IncorrectCloseDelim(char),
    /// Incorrect flags given to directive
    IncorrectFlags,
    /// Infinite loop detected in iteration directive `~{...~}`
    InfiniteLoop,
    /// Insufficient arguments to format string
    InsufficientArguments,
    /// Overflow converting a value to `Integer`
    IntegerOverflow,
    /// Invalid flags specifier
    InvalidFlags,
    /// Invalid radix to `~r` directive
    InvalidRadix(u32),
    /// Directive encountered where it is not expected
    MisplacedDirective,
    /// End of format string reached with open grouping directive
    MissingCloseDelim(char),
    /// Missing required branch within a conditional directive
    MissingBranch,
    /// End of branch directive found where end of conditional was expected
    ExtraBranch,
    /// Argument value of incorrect type received
    TypeError{
        /// Expected value type
        expected: &'static str,
        /// Type found
        found: &'static str,
    },
    /// Unrecognized directive character
    UnrecognizedDirective(char),
}

impl FormatError {
    /// Convenience function to return a `TypeError` value when `expected`
    /// type is expected, but some other type of value is found.
    pub fn expected(ty: &'static str, v: &Value) -> FormatError {
        FormatError::TypeError{
            expected: ty,
            found: v.type_name(),
        }
    }
}

impl fmt::Display for FormatError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FormatError::Error(ref s) => f.write_str(s),
            FormatError::ExtraFields => f.write_str("extraneous fields to directive"),
            FormatError::FieldTypeError{expected, found} =>
                write!(f, "expected field of type {}; found {}", expected, found),
            FormatError::FieldOverflow => f.write_str("integer overflow in field"),
            FormatError::IncompleteDirective => f.write_str("end of format string reached when parsing directive"),
            FormatError::IncorrectCloseDelim(ch) => write!(f, "incorrect close delimiter: `{}`", ch),
            FormatError::IncorrectFlags => f.write_str("incorrect flags to directive"),
            FormatError::InfiniteLoop => f.write_str("infinite loop detected"),
            FormatError::InsufficientArguments => f.write_str("insufficient arguments"),
            FormatError::IntegerOverflow => f.write_str("integer overflow"),
            FormatError::InvalidFlags => f.write_str("invalid flags"),
            FormatError::InvalidRadix(n) => write!(f, "invalid radix: {}", n),
            FormatError::MisplacedDirective => f.write_str("directive not expected here"),
            FormatError::MissingCloseDelim(ch) => write!(f, "missing close delimiter `{}`", ch),
            FormatError::MissingBranch => f.write_str("missing branch directive"),
            FormatError::ExtraBranch => f.write_str("extraneous branch directive"),
            FormatError::TypeError{expected, found} =>
                write!(f, "expected {}; found {}", expected, found),
            FormatError::UnrecognizedDirective(ch) => write!(f, "unrecognized directive `{}`", ch),
        }
    }
}

/// Constructs a formatted string using given the format `fmt` and input values.
pub fn format_string(names: &NameStore, fmt: &str, values: &[Value])
        -> Result<String, ExecError> {
    let mut buf = String::new();
    let mut fmter = StringFormatter::new(fmt, names, values);
    fmter.format_string(&mut buf)?;
    fmter.finish()?;
    Ok(buf)
}

struct StringFormatter<'fmt, 'names, 'value> {
    /// Input format string; contains a substring for subgroups
    fmt: &'fmt str,
    /// Full format string; used in error messages
    full_fmt: &'fmt str,
    chars: CharIndices<'fmt>,
    values: &'value [Value],
    names: &'names NameStore,
    /// Stack of group specifiers
    groups: Vec<(Group, Span)>,
    /// Last group-closing directive
    close_dir: Option<Directive<'fmt>>,
    /// Set to `true` when a termination directive has been run
    terminate: bool,
    /// Set to `true` when a `~:^` termination directive has been run
    terminate_loop: bool,
    /// Set to `true` when a `~:^` directive should terminate
    parent_end: bool,
    /// Index of the next argument to be consumed;
    /// may be arbitrarily out of bounds
    arg_index: usize,
    /// Byte index in `fmt` at the beginning of the last char consumed
    last_index: usize,
    /// Byte index in `fmt` at the end of the last char consumed
    end_index: usize,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Group {
    CaseConversion,
    Conditional,
    Iteration,
    Justify,
}

impl Group {
    fn get_group(open: char) -> Option<Group> {
        match open {
            '(' => Some(Group::CaseConversion),
            '[' => Some(Group::Conditional),
            '{' => Some(Group::Iteration),
            '<' => Some(Group::Justify),
            _ => None
        }
    }

    fn close_delim(self) -> char {
        match self {
            Group::CaseConversion => ')',
            Group::Conditional => ']',
            Group::Iteration => '}',
            Group::Justify => '>',
        }
    }
}

#[derive(Copy, Clone, Debug)]
struct Directive<'fmt> {
    at: bool,
    colon: bool,
    command: char,
    fields: &'fmt str,
    span: Span,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Field {
    Empty,
    Integer(i32),
    Char(char),
    /// `#` argument; use the number of remaining arguments as the value
    ArgCount,
    /// `v` argument; take an argument as the value
    ArgValue,
}

struct FieldParser<'a> {
    s: &'a str,
    chars: CharIndices<'a>,
}

impl<'a> FieldParser<'a> {
    fn new(s: &str) -> FieldParser {
        FieldParser{s, chars: s.char_indices()}
    }

    fn rest(mut self) -> &'a str {
        match self.chars.next() {
            Some((ind, _)) => &self.s[ind..],
            None => &self.s[..0]
        }
    }

    fn next(&mut self) -> Result<Option<Field>, FormatError> {
        match self.chars.next() {
            Some((_, ',')) => Ok(Some(Field::Empty)),
            Some((_, '\'')) => {
                let field = self.chars.next().map(|(_, ch)| Field::Char(ch));
                // Consume trailing comma
                self.chars.next();
                Ok(field)
            }
            Some((_, 'v')) => {
                // Consume trailing comma
                self.chars.next();
                Ok(Some(Field::ArgValue))
            }
            Some((_, '#')) => {
                // Consume trailing comma
                self.chars.next();
                Ok(Some(Field::ArgCount))
            }
            Some((start, _)) => {
                let mut end = start + 1;
                loop {
                    match self.chars.next() {
                        Some((_, ch)) if ch.is_digit(10) => end += 1,
                        _ => break,
                    }
                }

                self.s[start..end].parse()
                    .map(|i| Some(Field::Integer(i)))
                    .map_err(|_| FormatError::FieldOverflow)
            }
            None => Ok(None),
        }
    }
}

impl<'fmt, 'names, 'value> StringFormatter<'fmt, 'names, 'value> {
    fn new(s: &'fmt str, names: &'names NameStore, values: &'value [Value])
            -> StringFormatter<'fmt, 'names, 'value> {
        StringFormatter{
            fmt: s,
            full_fmt: s,
            chars: s.char_indices(),
            values,
            names,
            groups: Vec::new(),
            close_dir: None,
            terminate: false,
            terminate_loop: false,
            parent_end: true,
            arg_index: 0,
            last_index: 0,
            end_index: 0,
        }
    }

    fn sub(&self, s: &'fmt str, values: &'value [Value])
            -> StringFormatter<'fmt, 'names, 'value> {
        StringFormatter{
            full_fmt: self.full_fmt,
            .. StringFormatter::new(s, self.names, values)
        }
    }

    fn format_string(&mut self, buf: &mut String) -> Result<(), ExecError> {
        while let Some(ch) = self.consume_char() {
            match ch {
                '~' => {
                    let dir = self.parse_directive()?;

                    match dir.command {
                        'a' => self.format_aesthetic(&dir, buf)?,
                        's' => self.format_standard(&dir, buf)?,
                        'c' => self.format_character(&dir, buf)?,
                        'f' => self.format_float(&dir, buf)?,
                        'e' => self.format_exponent(&dir, buf)?,
                        'r' => self.format_radix(&dir, buf)?,
                        'd' => self.format_integer(&dir, buf, 10)?,
                        'b' => self.format_integer(&dir, buf, 2)?,
                        'o' => self.format_integer(&dir, buf, 8)?,
                        'x' => self.format_integer(&dir, buf, 16)?,
                        'p' => self.format_plural(&dir, buf)?,
                        't' => self.format_tab(&dir, buf)?,
                        'z' => self.pretty_print(&dir, buf)?,
                        '?' => self.process_indirection(&dir, buf)?,
                        '*' => self.process_goto(&dir)?,
                        '<' => {
                            self.process_justification(&dir, buf)?;
                            if self.terminate {
                                break;
                            }
                        }
                        '(' => {
                            self.process_case_conversion(&dir, buf)?;
                            if self.terminate {
                                break;
                            }
                        }
                        '[' => {
                            self.process_conditional(&dir, buf)?;
                            if self.terminate {
                                break;
                            }
                        }
                        '{' => self.process_iteration(&dir, buf)?,
                        '>' => {
                            self.end_group(Group::Justify, dir)?;
                            break;
                        }
                        ')' => {
                            self.end_group(Group::CaseConversion, dir)?;
                            break;
                        }
                        ']' => {
                            self.end_group(Group::Conditional, dir)?;
                            break;
                        }
                        '}' => {
                            self.end_group(Group::Iteration, dir)?;
                            break;
                        }
                        '^' => if self.process_terminate(&dir)? {
                            self.terminate = true;
                            if dir.colon {
                                self.terminate_loop = true;
                            }
                            break;
                        },
                        ';' => if self.inside_group(Group::Conditional) {
                            self.close_dir = Some(dir);
                            break;
                        } else if !self.inside_group(Group::Justify) {
                            return Err(self.error(dir.span,
                                FormatError::MisplacedDirective));
                        },
                        '|' => self.repeat_char(&dir, buf, '\x0c')?,
                        '%' => self.repeat_char(&dir, buf, '\n')?,
                        '&' => self.fresh_line(&dir, buf)?,
                        '\n' => self.consume_whitespace(),
                        '~' => self.repeat_char(&dir, buf, '~')?,
                        ch => return Err(self.error(self.span_one(),
                            FormatError::UnrecognizedDirective(ch)))
                    }
                }
                ch => buf.push(ch),
            }
        }

        Ok(())
    }

    fn check_open_groups(&self) -> Result<(), ExecError> {
        match self.groups.last() {
            None => Ok(()),
            Some(&(group, span)) => Err(self.error(span,
                FormatError::MissingCloseDelim(group.close_delim())))
        }
    }

    fn finish(self) -> Result<(), ExecError> {
        self.check_open_groups()
    }

    fn push_group(&mut self, group: Group, span: Span) {
        self.groups.push((group, span));
    }

    fn pop_group(&mut self) {
        self.groups.pop();
    }

    fn end_group(&mut self, group: Group, dir: Directive<'fmt>) -> Result<(), ExecError> {
        match self.groups.last() {
            Some(&(grp, _)) if grp == group => {
                // Store the directive that closed the group
                self.close_dir = Some(dir);
                Ok(())
            }
            _ => Err(self.error(dir.span,
                FormatError::IncorrectCloseDelim(group.close_delim())))
        }
    }

    fn parse_directive(&mut self) -> Result<Directive<'fmt>, ExecError> {
        let start = self.last_index;
        let field_start = self.end_index;

        'fields: loop {
            match self.peek_char() {
                Some('\'') => {
                    self.consume_char();
                    // Next is any char
                    match self.consume_char() {
                        Some(_) => (),
                        None => break
                    }
                    // Next is nothing or comma
                    match self.peek_char() {
                        Some(',') => { self.consume_char(); }
                        _ => break
                    }
                    continue;
                }
                Some(',') => (),
                Some('v') | Some('#') => {
                    self.consume_char();
                    match self.peek_char() {
                        Some(',') => { self.consume_char(); },
                        _ => break
                    }
                }
                Some(ch) if ch == '-' || ch.is_digit(10) => {
                    self.consume_char();
                    loop {
                        match self.peek_char() {
                            Some(ch) if ch.is_digit(10) => {
                                self.consume_char();
                            }
                            Some(',') => break,
                            _ => break 'fields
                        }
                    }
                }
                _ => break
            }
            self.consume_char();
        }

        let field_end = self.end_index;
        let fields = &self.fmt[field_start..field_end];

        let mut at = false;
        let mut colon = false;

        loop {
            match self.consume_char() {
                Some('@') => {
                    if at {
                        return Err(self.error(self.span_one(),
                            FormatError::InvalidFlags));
                    }
                    at = true;
                }
                Some(':') => {
                    if colon {
                        return Err(self.error(self.span_one(),
                            FormatError::InvalidFlags));
                    }
                    colon = true;
                }
                Some(ch) => {
                    return Ok(Directive{
                        at,
                        colon,
                        command: ch.to_ascii_lowercase(),
                        fields,
                        span: self.span_start(start),
                    })
                }
                None => return Err(self.error(self.span_start(start),
                    FormatError::IncompleteDirective))
            }
        }
    }

    fn pretty_print(&mut self, dir: &Directive, buf: &mut String)
            -> Result<(), ExecError> {
        let mut fields = FieldParser::new(dir.fields);
        let indent = self.get_u32_field(&mut fields, dir.span)?.unwrap_or(0);
        self.no_fields(fields, dir.span)?;

        let arg = self.consume_arg(dir.span)?;

        let _ = pretty_print(buf, self.names, arg, indent);

        Ok(())
    }

    fn format_aesthetic(&mut self, dir: &Directive, buf: &mut String)
            -> Result<(), ExecError> {
        let mut fields = FieldParser::new(dir.fields);
        let min_col = self.get_u32_field(&mut fields, dir.span)?.unwrap_or(0);
        let col_inc = self.get_u32_field(&mut fields, dir.span)?.unwrap_or(0);
        let min_pad = self.get_u32_field(&mut fields, dir.span)?.unwrap_or(0);
        let pad_char = self.get_char_field(&mut fields, dir.span)?.unwrap_or(' ');
        self.no_fields(fields, dir.span)?;

        let arg = self.consume_arg(dir.span)?;

        let s = display_names(self.names, arg).to_string();
        pad_str(buf, &s, min_col, col_inc, min_pad, pad_char, dir.at);
        Ok(())
    }

    fn format_standard(&mut self, dir: &Directive, buf: &mut String)
            -> Result<(), ExecError> {
        let mut fields = FieldParser::new(dir.fields);
        let min_col = self.get_u32_field(&mut fields, dir.span)?.unwrap_or(0);
        let col_inc = self.get_u32_field(&mut fields, dir.span)?.unwrap_or(0);
        let min_pad = self.get_u32_field(&mut fields, dir.span)?.unwrap_or(0);
        let pad_char = self.get_char_field(&mut fields, dir.span)?.unwrap_or(' ');
        self.no_fields(fields, dir.span)?;

        let arg = self.consume_arg(dir.span)?;
        let s = debug_names(self.names, arg).to_string();
        pad_str(buf, &s, min_col, col_inc, min_pad, pad_char, dir.at);
        Ok(())
    }

    fn format_character(&mut self, dir: &Directive, buf: &mut String)
            -> Result<(), ExecError> {
        // TODO: ':' flag prints name for special characters, e.g. "Space";
        // '@' flag prints name in literal format, e.g. "#\Space"
        self.no_fields(FieldParser::new(dir.fields), dir.span)?;
        let arg = self.consume_arg(dir.span)?;

        let ch = match *arg {
            Value::Char(ch) => ch,
            ref v => return Err(self.error(dir.span, FormatError::expected("char", v)))
        };

        buf.push(ch);
        Ok(())
    }

    fn no_fields(&self, mut fields: FieldParser, span: Span) -> Result<(), ExecError> {
        match fields.next() {
            Ok(None) => Ok(()),
            _ => Err(self.error(span, FormatError::ExtraFields))
        }
    }

    fn fresh_line(&mut self, dir: &Directive, buf: &mut String) -> Result<(), ExecError> {
        let mut fields = FieldParser::new(dir.fields);
        let mut n = self.get_u32_field(&mut fields, dir.span)?.unwrap_or(1);
        self.no_fields(fields, dir.span)?;

        if buf.is_empty() || buf.ends_with('\n') {
            n = n.saturating_sub(1);
        }

        buf.extend(repeat('\n').take(n as usize));
        Ok(())
    }

    fn repeat_char(&mut self, dir: &Directive, buf: &mut String, ch: char) -> Result<(), ExecError> {
        let mut fields = FieldParser::new(dir.fields);

        let n = self.get_u32_field(&mut fields, dir.span)?.unwrap_or(1);
        self.no_fields(fields, dir.span)?;

        buf.extend(repeat(ch).take(n as usize));

        Ok(())
    }

    fn format_plural(&mut self, dir: &Directive, buf: &mut String)
            -> Result<(), ExecError> {
        self.no_fields(FieldParser::new(dir.fields), dir.span)?;

        if dir.colon {
            self.goto_back_arg(1);
        }

        let arg = self.consume_arg(dir.span)?;
        let is_one = match *arg {
            Value::Float(f) => f == 1.0,
            Value::Integer(ref i) => i == &Integer::one(),
            Value::Ratio(ref r) => r.numer() == r.denom(),
            ref v => return Err(self.error(dir.span,
                FormatError::expected("number", v)))
        };

        match (dir.at, is_one) {
            (false, true) => (),
            (false, false) => buf.push('s'),
            (true, true) => buf.push('y'),
            (true, false) => buf.push_str("ies"),
        }

        Ok(())
    }

    fn format_tab(&mut self, dir: &Directive, buf: &mut String) -> Result<(), ExecError> {
        let mut fields = FieldParser::new(dir.fields);

        let col_num = self.get_u32_field(&mut fields, dir.span)?.unwrap_or(1);
        let col_inc = self.get_u32_field(&mut fields, dir.span)?.unwrap_or(1);
        self.no_fields(fields, dir.span)?;

        let cur_col = cur_line_len(&buf) as u32;

        if !dir.at {
            if cur_col < col_num {
                buf.extend(repeat(' ').take((col_num - cur_col) as usize));
            } else if col_inc != 0 {
                let n = col_inc - (cur_col % col_inc);
                buf.extend(repeat(' ').take(n as usize));
            }
        } else {
            let n = if col_inc > 1 {
                col_num + col_inc - 1 - ((cur_col + col_num) - 1) % col_inc
            } else {
                col_num
            };
            buf.extend(repeat(' ').take(n as usize));
        }

        Ok(())
    }

    fn format_float(&mut self, dir: &Directive, buf: &mut String)
            -> Result<(), ExecError> {
        let mut fields = FieldParser::new(dir.fields);
        let width = self.get_u32_field(&mut fields, dir.span)?;
        let prec = self.get_u32_field(&mut fields, dir.span)?;
        let pad_char = self.get_char_field(&mut fields, dir.span)?.unwrap_or(' ');
        self.no_fields(fields, dir.span)?;

        let arg = self.consume_arg(dir.span)?;
        let f = self.get_float(arg, dir.span)?;

        // This is horrible and hacky because there's no way I'm implementing
        // float formatting myself. Deal with it.
        let s = match (dir.at, width, prec) {
            (false, None,    None   ) => format!("{}",        f),
            (false, Some(w), None   ) => format!("{:1$}",     f, w as usize),
            (false, None,    Some(p)) => format!("{:.1$}",    f,             p as usize),
            (false, Some(w), Some(p)) => format!("{:1$.2$}",  f, w as usize, p as usize),
            (true,  None,    None   ) => format!("{:+}",      f),
            (true,  Some(w), None   ) => format!("{:+1$}",    f, w as usize),
            (true,  None,    Some(p)) => format!("{:+.1$}",   f,             p as usize),
            (true,  Some(w), Some(p)) => format!("{:+1$.2$}", f, w as usize, p as usize),
        };

        if pad_char != ' ' {
            buf.extend(s.chars().map(|ch| if ch == ' ' { pad_char } else { ch }));
        } else {
            buf.push_str(&s);
        }

        Ok(())
    }

    fn format_exponent(&mut self, dir: &Directive, buf: &mut String)
            -> Result<(), ExecError> {
        let mut fields = FieldParser::new(dir.fields);
        let width = self.get_u32_field(&mut fields, dir.span)?;
        let prec = self.get_u32_field(&mut fields, dir.span)?;
        let pad_char = self.get_char_field(&mut fields, dir.span)?.unwrap_or(' ');
        self.no_fields(fields, dir.span)?;

        let arg = self.consume_arg(dir.span)?;
        let f = self.get_float(arg, dir.span)?;

        // This is horrible and hacky because there's no way I'm implementing
        // float formatting myself. Deal with it.
        let s = match (dir.at, width, prec) {
            (false, None,    None   ) => format!("{:e}",       f),
            (false, Some(w), None   ) => format!("{:1$e}",     f, w as usize),
            (false, None,    Some(p)) => format!("{:.1$e}",    f,             p as usize),
            (false, Some(w), Some(p)) => format!("{:1$.2$e}",  f, w as usize, p as usize),
            (true,  None,    None   ) => format!("{:+e}",      f),
            (true,  Some(w), None   ) => format!("{:+1$e}",    f, w as usize),
            (true,  None,    Some(p)) => format!("{:+.1$e}",   f,             p as usize),
            (true,  Some(w), Some(p)) => format!("{:+1$.2$e}", f, w as usize, p as usize),
        };

        if pad_char != ' ' {
            buf.extend(s.chars().map(|ch| if ch == ' ' { pad_char } else { ch }));
        } else {
            buf.push_str(&s);
        }

        Ok(())
    }

    fn format_radix(&mut self, dir: &Directive, buf: &mut String)
            -> Result<(), ExecError> {
        let mut fields = FieldParser::new(dir.fields);

        match self.get_u32_field(&mut fields, dir.span)? {
            Some(n) if n >= 2 && n <= 36 => {
                let new_dir = Directive{fields: fields.rest(), ..*dir};
                return self.format_integer(&new_dir, buf, n);
            }
            Some(n) => return Err(self.error(dir.span, FormatError::InvalidRadix(n))),
            None => ()
        }

        let arg = self.consume_arg(dir.span)?;
        let i = self.get_integer(arg, dir.span)?;

        let n = match (dir.at, i.to_u32()) {
            (false, Some(n)) if n <= 5000 => n,
            (true, Some(n)) if n > 0 && n <= 5000 => n,
            (false, _) => return Err(self.error(dir.span,
                FormatError::Error(format!(
                    "Expected an integer 0 - 5000; found {}", i)
                        .into_boxed_str()))),
            (true, _) => return Err(self.error(dir.span,
                FormatError::Error(format!(
                    "Expected an integer 1 - 5000; found {}", i)
                        .into_boxed_str())))
        };

        match (dir.at, dir.colon) {
            (false, false) => self.format_cardinal(n, buf),
            (false, true) => self.format_ordinal(n, buf),
            (true, colon) => self.format_roman_numeral(n, buf, colon)
        }
    }

    fn format_integer(&mut self, dir: &Directive, buf: &mut String,
            radix: u32) -> Result<(), ExecError> {
        let mut fields = FieldParser::new(dir.fields);
        let min_col = self.get_u32_field(&mut fields, dir.span)?.unwrap_or(0);
        let pad_char = self.get_char_field(&mut fields, dir.span)?.unwrap_or(' ');
        let comma = self.get_char_field(&mut fields, dir.span)?.unwrap_or(',');
        let comma_interval = self.get_u32_field(&mut fields, dir.span)?.unwrap_or(3);
        self.no_fields(fields, dir.span)?;

        let arg = self.consume_arg(dir.span)?;
        let i = self.get_integer(arg, dir.span)?;

        let mut s = i.abs().to_str_radix(radix);

        if dir.colon {
            let mut n = s.len();
            while n > comma_interval as usize {
                n -= comma_interval as usize;
                s.insert(n, comma);
            }
        }

        if dir.at || i.is_negative() {
            let sign = if i.is_negative() { '-' } else { '+' };
            s.insert(0, sign);
        }

        pad_str(buf, &s, min_col, 0, 0, pad_char, true);

        Ok(())
    }

    fn consume_char(&mut self) -> Option<char> {
        match self.chars.next() {
            Some((ind, ch)) => {
                self.last_index = ind;
                self.end_index = ind + ch.len_utf8();
                Some(ch)
            }
            None => None
        }
    }

    fn consume_whitespace(&mut self) {
        while let Some(ch) = self.peek_char() {
            if ch != '\n' && ch.is_whitespace() {
                self.consume_char();
            } else {
                break;
            }
        }
    }

    fn peek_char(&mut self) -> Option<char> {
        match self.chars.clone().next() {
            Some((_, ch)) => Some(ch),
            None => None
        }
    }

    fn arguments_empty(&self) -> bool {
        self.arg_index >= self.values.len()
    }

    fn args_left(&self) -> usize {
        self.values.len().saturating_sub(self.arg_index)
    }

    fn consume_arg(&mut self, span: Span) -> Result<&'value Value, ExecError> {
        if self.arg_index >= self.values.len() {
            Err(self.error(span, FormatError::InsufficientArguments))
        } else {
            let ind = self.arg_index;
            self.arg_index += 1;
            Ok(&self.values[ind])
        }
    }

    fn inside_group(&self, group: Group) -> bool {
        match self.groups.last() {
            Some(&(grp, _)) => grp == group,
            _ => false
        }
    }

    fn process_case_conversion(&mut self, dir: &Directive, buf: &mut String) -> Result<(), ExecError> {
        self.no_fields(FieldParser::new(dir.fields), dir.span)?;
        self.push_group(Group::CaseConversion, dir.span);
        let start = buf.len();

        self.format_string(buf)?;
        self.pop_group();

        if !buf[start..].is_empty() {
            // none - lowercase
            // '@'  - capitalize first letter
            // ':'  - title case (capitalize first letter of each word)
            // '@:' - uppercase
            match (dir.at, dir.colon) {
                (false, false) => make_lowercase(buf, start),
                (true, false) => make_first_uppercase(buf, start),
                (false, true) => make_title_case(buf, start),
                (true, true) => make_uppercase(buf, start)
            }
        }

        Ok(())
    }

    fn process_conditional(&mut self, dir: &Directive, buf: &mut String) -> Result<(), ExecError> {
        self.push_group(Group::Conditional, dir.span);
        let mut found_end = false;

        match (dir.at, dir.colon) {
            (true, true) => return Err(self.error(dir.span,
                FormatError::IncorrectFlags)),
            (false, false) => {
                // No-flag conditional; argument is an integer referring to
                // the desired branch to evaluate.
                // If there's no arg to consume, just move on silently.
                if let Ok(arg) = self.consume_arg(dir.span) {
                    let i = self.get_integer(arg, dir.span)?;
                    let n = match i.to_u32() {
                        Some(n) => n,
                        None => u32::max_value()
                    };

                    // Skip to the branch we're looking for
                    for _ in 0..n {
                        let dir = self.skip_until(
                            |dir| dir.command == ';' || dir.command == ']')?;

                        match dir {
                            // End branch. Break out.
                            Directive{command: ']', ..} => {
                                found_end = true;
                                break;
                            }
                            // Else branch. Unconditionally evaluate.
                            Directive{command: ';', colon: true, ..} => {
                                break;
                            }
                            _ => ()
                        }
                    }

                    if !found_end {
                        self.format_string(buf)?;

                        if let Some(Directive{command: ']', ..}) = self.close_dir.take() {
                             found_end = true;
                        }
                    }
                }
            }
            (false, true) => {
                // ':' conditional; argument is a bool. If false, evaluate
                // first branch. If true, evaluate second branch.
                let arg = self.consume_arg(dir.span)?;
                let v = self.get_bool(arg, dir.span)?;

                if v {
                    let dir = self.skip_until(
                        |dir| dir.command == ';' || dir.command == ']')?;

                    if dir.command == ']' {
                        return Err(self.error(dir.span, FormatError::MissingBranch));
                    }
                }

                self.format_string(buf)?;

                match self.close_dir.take() {
                    Some(Directive{command: ']', ..}) => found_end = true,
                    Some(Directive{command: ';', ..}) => if v {
                        return Err(self.error(dir.span, FormatError::ExtraBranch))
                    },
                    _ => ()
                }
            }
            (true, false) => {
                // '@' conditional; argument may be any value.
                // If it is `()`, the arg is consumed and the branch skipped.
                // Otherwise, the arg is not consumed and the single contained
                // branch is evaluated.
                let arg = self.consume_arg(dir.span)?;
                if let Value::Unit = *arg {
                    // Nothing
                } else {
                    self.goto_back_arg(1);
                    self.format_string(buf)?;

                    match self.close_dir.take() {
                        Some(Directive{command: ']', ..}) => found_end = true,
                        Some(Directive{command: ';', ..}) =>
                            return Err(self.error(dir.span,
                                FormatError::ExtraBranch)),
                        _ => ()
                    }
                }
            }
        }

        if !found_end {
            self.skip_until(|dir| dir.command == ']')?;
        }

        self.pop_group();

        Ok(())
    }

    fn process_justification(&mut self, dir: &Directive, buf: &mut String) -> Result<(), ExecError> {
        self.push_group(Group::Justify, dir.span);
        let mut line_len = 72;
        let mut pre = None;
        let mut strs = Vec::new();

        let mut fields = FieldParser::new(dir.fields);
        let min_col = self.get_u32_field(&mut fields, dir.span)?.unwrap_or(0);
        let col_inc = self.get_u32_field(&mut fields, dir.span)?.unwrap_or(1);
        let min_pad = self.get_u32_field(&mut fields, dir.span)?.unwrap_or(0);
        let pad_char = self.get_char_field(&mut fields, dir.span)?.unwrap_or(' ');
        self.no_fields(fields, dir.span)?;

        loop {
            let seg_start = self.end_index;

            let end_dir = self.skip_until(
                |dir| dir.command == ';' || dir.command == '>')?;

            // Special `~:;` directive must be the first.
            if let Directive{command: ';', colon: true, ..} = end_dir {
                if !strs.is_empty() {
                    return Err(self.error(end_dir.span,
                        FormatError::MisplacedDirective));
                }
            }

            let mut s = String::new();

            let segment = &self.fmt[seg_start..end_dir.span.lo as usize];
            let mut sub_fmter = self.sub(segment, self.values);
            sub_fmter.arg_index = self.arg_index;

            sub_fmter.format_string(&mut s)?;
            self.arg_index = sub_fmter.arg_index;
            if sub_fmter.terminate {
                break;
            }
            sub_fmter.finish()?;

            if let Directive{command: ';', colon: true, ..} = end_dir {
                pre = Some(s);

                let mut fields = FieldParser::new(end_dir.fields);
                let spare = self.get_u32_field(&mut fields, end_dir.span)?
                    .unwrap_or(0);
                if let Some(len) = self.get_u32_field(&mut fields, end_dir.span)? {
                    line_len = len.saturating_sub(spare);
                }
                self.no_fields(fields, end_dir.span)?;
            } else {
                strs.push(s);
            }

            if end_dir.command == '>' {
                break;
            }
        }

        if strs.is_empty() {
            buf.extend(repeat(pad_char).take(min_col as usize));
        } else {
            // Number of padding spans
            let mut pads = match strs.len() as u32 - 1 + (dir.at as u32) + (dir.colon as u32) {
                0 => 1,
                n => n,
            };

            let total_text = strs.iter().map(|s| s.len() as u32).sum::<u32>();
            let cols = max(min_col, total_text + pads * min_pad);
            let cols = cols + ((cols + (col_inc - 1)) % col_inc);
            let total_pad = cols - total_text;

            let base_pad = total_pad / pads;
            let mut extra_pad = total_pad % pads;

            let mut temp = String::new();

            if dir.colon || (strs.len() == 1 && !dir.at) {
                let pad = if extra_pad == 0 {
                    base_pad
                } else {
                    extra_pad -= 1;
                    base_pad + 1
                };

                pads -= 1;
                temp.extend(repeat(pad_char).take(pad as usize));
            }

            for s in &strs {
                temp.push_str(s);
                if pads != 0 {
                    pads -= 1;
                    let pad = if extra_pad == 0 {
                        base_pad
                    } else {
                        extra_pad -= 1;
                        base_pad + 1
                    };

                    temp.extend(repeat(pad_char).take(pad as usize));
                }
            }

            if let Some(pre) = pre {
                if cur_line_len(&buf) + temp.len() > line_len as usize {
                    buf.push_str(&pre);
                }
            }
            buf.push_str(&temp);
        }

        self.pop_group();
        Ok(())
    }

    fn process_terminate(&mut self, dir: &Directive) -> Result<bool, ExecError> {
        let mut fields = FieldParser::new(dir.fields);
        let a = self.get_u32_field(&mut fields, dir.span)?;
        let b = self.get_u32_field(&mut fields, dir.span)?;
        let c = self.get_u32_field(&mut fields, dir.span)?;
        self.no_fields(fields, dir.span)?;

        Ok(match (a, b, c) {
            (None,    _,       _) => if dir.colon {
                self.parent_end
            } else {
                self.arguments_empty()
            },
            (Some(a), None,    _) => a == 0,
            (Some(a), Some(b), None) => a == b,
            (Some(a), Some(b), Some(c)) => a <= b && b <= c
        })
    }

    /// Advances over text in the stream, without processing it.
    /// When a directive is reached, the predicate is called to determine
    /// whether the directive terminates the skip operation.
    /// This directive is then returned.
    /// If a subgroup directive is encountered, that group and any contained
    /// directives will be ignored.
    /// If the end of the input stream is reached before a matching directive,
    /// the error result of `check_open_groups` will be returned.
    /// If `check_open_groups` does not return an error, it will panic.
    fn skip_until<F>(&mut self, mut f: F) -> Result<Directive<'fmt>, ExecError>
            where F: FnMut(&Directive) -> bool {
        let mut groups = Vec::new();

        loop {
            match self.consume_char() {
                Some('~') => {
                    let dir = self.parse_directive()?;

                    match dir.command {
                        '<' | '(' | '[' | '{' => {
                            let group = Group::get_group(dir.command).unwrap();

                            groups.push((group.close_delim(), dir.span));
                            continue;
                        }
                        '>' | ')' | ']' | '}' if !groups.is_empty() => {
                            let (ch, span) = groups.pop().unwrap();

                            if ch != dir.command {
                                return Err(self.error(span,
                                    FormatError::IncorrectCloseDelim(dir.command)));
                            }
                            continue;
                        }
                        _ => ()
                    }

                    if groups.is_empty() && f(&dir) {
                        return Ok(dir);
                    }
                }
                Some(_) => (),
                None => break,
            }
        }

        if let Some((ch, span)) = groups.pop() {
            return Err(self.error(span,
                FormatError::MissingCloseDelim(ch)));
        }

        self.check_open_groups()?;
        panic!("skip_until reached end with no open group");
    }

    fn goto_back_arg(&mut self, n: usize) {
        self.arg_index = self.arg_index.saturating_sub(n);
    }

    fn goto_fwd_arg(&mut self, n: usize) {
        self.arg_index = self.arg_index.saturating_add(n);
    }

    fn process_goto(&mut self, dir: &Directive) -> Result<(), ExecError> {
        let mut fields = FieldParser::new(dir.fields);
        let n = self.get_u32_field(&mut fields, dir.span)?;
        self.no_fields(fields, dir.span)?;

        if dir.at {
            self.arg_index = n.unwrap_or(0) as usize;
        } else {
            let n = n.unwrap_or(1) as usize;
            if dir.colon {
                self.goto_back_arg(n)
            } else {
                self.goto_fwd_arg(n)
            }
        }

        Ok(())
    }

    fn process_indirection(&mut self, dir: &Directive, buf: &mut String) -> Result<(), ExecError> {
        self.no_fields(FieldParser::new(dir.fields), dir.span)?;

        let arg = self.consume_arg(dir.span)?;
        let sub_fmt = self.get_string(arg, dir.span)?;

        if !dir.at {
            let arg = self.consume_arg(dir.span)?;
            let sub_args = self.get_list(arg, dir.span)?;

            let mut sub_fmter = self.sub(sub_fmt, sub_args);
            sub_fmter.format_string(buf)?;
            sub_fmter.finish()?;
        } else {
            let mut sub_fmter = self.sub(sub_fmt, self.values);
            sub_fmter.arg_index = self.arg_index;
            sub_fmter.format_string(buf)?;
            self.arg_index = sub_fmter.arg_index;
            sub_fmter.finish()?;
        }

        Ok(())
    }

    fn process_iteration(&mut self, dir: &Directive, buf: &mut String) -> Result<(), ExecError> {
        self.push_group(Group::Iteration, dir.span);

        let mut fields = FieldParser::new(dir.fields);
        let mut max_iter = self.get_u32_field(&mut fields, dir.span)?
            .unwrap_or(u32::max_value());
        self.no_fields(fields, dir.span)?;

        let start = self.end_index;
        let end_dir = self.skip_until(|dir| dir.command == '}')?;

        let sub_fmt = match &self.fmt[start..end_dir.span.lo as usize] {
            fmt if fmt.is_empty() => {
                let arg = self.consume_arg(dir.span)?;
                self.get_string(arg, dir.span)?
            }
            fmt => fmt
        };

        // Whether to run sub_fmt at least once
        let run_once = end_dir.colon;

        match (dir.at, dir.colon) {
            (false, false) => {
                // No-flag; consumes a list arg.
                let arg = self.consume_arg(dir.span)?;
                let li = self.get_list(arg, dir.span)?;
                let mut last_off = 0;

                while last_off < li.len() {
                    if max_iter == 0 {
                        break;
                    }
                    max_iter -= 1;
                    let mut sub_fmter = self.sub(sub_fmt, &li[last_off..]);

                    sub_fmter.format_string(buf)?;
                    let new_off = last_off.saturating_add(sub_fmter.arg_index);
                    if sub_fmter.terminate {
                        break;
                    }
                    sub_fmter.finish()?;

                    if last_off == new_off {
                        // If no arguments were consumed, it's an infinite loop.
                        return Err(self.error(dir.span, FormatError::InfiniteLoop));
                    }
                    last_off = new_off;
                }

                if li.is_empty() && run_once && max_iter != 0 {
                    let mut sub_fmter = self.sub(sub_fmt, &[]);

                    sub_fmter.format_string(buf)?;
                    sub_fmter.finish()?;
                }
            }
            (true, false) => {
                // '@' flag; iterations consume args from the parent argument list.
                let start_off = self.arg_index;
                let mut last_off = start_off;

                while last_off < self.values.len() {
                    if max_iter == 0 {
                        break;
                    }
                    max_iter -= 1;
                    let mut sub_fmter = self.sub(sub_fmt, self.values);
                    sub_fmter.arg_index = last_off;

                    sub_fmter.format_string(buf)?;
                    let new_off = sub_fmter.arg_index;
                    if sub_fmter.terminate {
                        break;
                    }
                    sub_fmter.finish()?;

                    if new_off <= last_off {
                        // If no arguments were consumed, it's an infinite loop.
                        return Err(self.error(dir.span, FormatError::InfiniteLoop));
                    }
                    last_off = new_off;
                }

                if start_off >= self.values.len() && run_once && max_iter != 0 {
                    let mut sub_fmter = self.sub(sub_fmt, &[]);
                    sub_fmter.arg_index = start_off;

                    sub_fmter.format_string(buf)?;
                    last_off = sub_fmter.arg_index;
                    sub_fmter.finish()?;
                }

                self.arg_index = last_off;
            }
            (false, true) => {
                // ':' flag; consumes a list arg whose elements must be lists.
                // Each iteration receives a sublist.
                let arg = self.consume_arg(dir.span)?;
                let li = self.get_list(arg, dir.span)?;

                for (i, item) in li.iter().enumerate() {
                    if max_iter == 0 {
                        break;
                    }
                    max_iter -= 1;
                    let sub_li = self.get_list(item, dir.span)?;
                    let mut sub_fmter = self.sub(sub_fmt, sub_li);

                    if i + 1 < li.len() {
                        sub_fmter.parent_end = false;
                    }

                    sub_fmter.format_string(buf)?;
                    if sub_fmter.terminate_loop {
                        break;
                    } else if sub_fmter.terminate {
                        continue;
                    }
                    sub_fmter.finish()?;
                }

                if li.is_empty() && run_once && max_iter != 0 {
                    let mut sub_fmter = self.sub(sub_fmt, &[]);

                    sub_fmter.format_string(buf)?;
                    sub_fmter.finish()?;
                }
            }
            (true, true) => {
                // ':@' flags; iteration uses parent arg list and expects sublists.
                let start_off = self.arg_index;

                if start_off >= self.values.len() {
                    if run_once && max_iter != 0 {
                        let mut sub_fmter = self.sub(sub_fmt, &[]);

                        sub_fmter.format_string(buf)?;
                        sub_fmter.finish()?;
                    }
                } else {
                    for (i, item) in self.values[start_off..].iter().enumerate() {
                        if max_iter == 0 {
                            break;
                        }
                        max_iter -= 1;
                        let sub_li = self.get_list(item, dir.span)?;

                        let mut sub_fmter = self.sub(sub_fmt, sub_li);

                        if i + start_off + 1 < self.values.len() {
                            sub_fmter.parent_end = false;
                        }

                        sub_fmter.format_string(buf)?;
                        if sub_fmter.terminate_loop {
                            break;
                        } else if sub_fmter.terminate {
                            continue;
                        }
                        sub_fmter.finish()?;
                    }
                }
            }
        }

        self.pop_group();
        Ok(())
    }

    fn format_cardinal(&mut self, mut n: u32, buf: &mut String) -> Result<(), ExecError> {
        if n == 0 {
            buf.push_str("zero");
            return Ok(());
        }

        if n >= 1000 {
            buf.push_str(low_cardinal(n / 1000).0);
            buf.push(' ');
            buf.push_str("thousand ");
            n %= 1000;
        }

        if n >= 100 {
            buf.push_str(low_cardinal(n / 100).0);
            buf.push(' ');
            buf.push_str("hundred ");
            n %= 100;
        }

        if n >= 20 {
            buf.push_str(mid_cardinal(n / 10).0);
            n %= 10;
            if n != 0 {
                buf.push('-');
            }
        }

        if n != 0 {
            buf.push_str(low_cardinal(n).0);
        }

        if buf.ends_with(' ') {
            buf.pop(); // Remove trailing space
        }
        Ok(())
    }

    fn format_ordinal(&mut self, mut n: u32, buf: &mut String) -> Result<(), ExecError> {
        if n == 0 {
            buf.push_str("zeroth");
            return Ok(());
        }

        if n >= 1000 {
            buf.push_str(low_cardinal(n / 1000).0);
            buf.push(' ');
            n %= 1000;
            if n == 0 {
                buf.push_str("thousandth");
            } else {
                buf.push_str("thousand ");
            }
        }

        if n >= 100 {
            buf.push_str(low_cardinal(n / 100).0);
            buf.push(' ');
            n %= 100;
            if n == 0 {
                buf.push_str("hundredth");
            } else {
                buf.push_str("hundred ");
            }
        }

        if n >= 20 {
            let mid = n / 10;
            n %= 10;

            if n == 0 {
                buf.push_str(mid_cardinal(mid).1);
            } else {
                buf.push_str(mid_cardinal(mid).0);
                buf.push('-');
            }
        }

        if n != 0 {
            buf.push_str(low_cardinal(n).1);
        }

        Ok(())
    }

    fn format_roman_numeral(&mut self, mut n: u32, buf: &mut String, old: bool)
            -> Result<(), ExecError> {
        while n > 0 {
            match get_roman_digit(n, old) {
                Roman::One(ch, value) => {
                    buf.push(ch);
                    n -= value;
                }
                Roman::Two(a, b, value) => {
                    buf.push(a);
                    buf.push(b);
                    n -= value;
                }
            }
        }

        Ok(())
    }

    fn error(&self, span: Span, err: FormatError) -> ExecError {
        let off = substr_offset(self.fmt, self.full_fmt) as BytePos;

        ExecError::FormatError{
            fmt: self.full_fmt.to_owned().into_boxed_str(),
            span: Span{lo: span.lo + off, hi: span.hi + off},
            err,
        }
    }

    fn get_bool(&self, v: &Value, span: Span) -> Result<bool, ExecError> {
        match *v {
            Value::Bool(r) => Ok(r),
            ref v => Err(self.error(span, FormatError::expected("bool", v)))
        }
    }

    fn get_char_field(&mut self, fields: &mut FieldParser, span: Span)
            -> Result<Option<char>, ExecError> {
        let r = fields.next().map_err(|e| self.error(span, e));

        match r? {
            None => Ok(None),
            Some(Field::Empty) => Ok(None),
            Some(Field::Char(ch)) => Ok(Some(ch)),
            Some(Field::ArgValue) => {
                let arg = self.consume_arg(span)?;
                match *arg {
                    Value::Char(ch) => Ok(Some(ch)),
                    ref v => Err(self.error(span,
                        FormatError::expected("char", v)))
                }
            }
            Some(Field::ArgCount) | Some(Field::Integer(_)) =>
                Err(self.error(span, FormatError::FieldTypeError{
                    expected: "char",
                    found: "integer",
                })),
        }
    }

    fn get_u32_field(&mut self, fields: &mut FieldParser, span: Span)
            -> Result<Option<u32>, ExecError> {
        let r = fields.next().map_err(|e| self.error(span, e));

        match r? {
            None => Ok(None),
            Some(Field::Empty) => Ok(None),
            Some(Field::Integer(i)) => match i.to_u32() {
                Some(u) if u <= 100 => Ok(Some(u)),
                _ => Err(self.error(span, FormatError::FieldOverflow))
            },
            Some(Field::ArgCount) => Ok(Some(self.args_left() as u32)),
            Some(Field::ArgValue) => {
                let arg = self.consume_arg(span)?;
                match self.get_integer(arg, span)?.to_u32() {
                    Some(u) if u <= 100 => Ok(Some(u)),
                    _ => Err(self.error(span, FormatError::FieldOverflow))
                }
            }
            Some(Field::Char(_)) => Err(self.error(span,
                FormatError::FieldTypeError{
                    expected: "integer",
                    found: "char",
                })),
        }
    }

    fn get_float(&self, v: &Value, span: Span) -> Result<f64, ExecError> {
        match *v {
            Value::Float(f) => Ok(f),
            Value::Integer(ref i) => match i.to_f64() {
                Some(f) => Ok(f),
                None if i.is_negative() => Ok(-f64::INFINITY),
                None => Ok(f64::INFINITY)
            },
            Value::Ratio(ref r) => match r.to_f64() {
                Some(f) => Ok(f),
                None if r.is_negative() => Ok(-f64::INFINITY),
                None => Ok(f64::INFINITY)
            },
            ref v => Err(self.error(span, FormatError::expected("float", v)))
        }
    }

    fn get_integer<'a>(&self, v: &'a Value, span: Span)
            -> Result<Cow<'a, Integer>, ExecError> {
        match *v {
            Value::Float(f) => Integer::from_f64(f)
                .map(Owned)
                .ok_or_else(|| self.error(span, FormatError::IntegerOverflow)),
            Value::Integer(ref i) => Ok(Borrowed(i)),
            Value::Ratio(ref r) => Ok(Owned(r.to_integer())),
            ref v => Err(self.error(span, FormatError::expected("integer", v)))
        }
    }

    fn get_list<'a>(&self, v: &'a Value, span: Span)
            -> Result<&'a [Value], ExecError> {
        match *v {
            Value::Unit => Ok(&[][..]),
            Value::List(ref li) => Ok(li),
            ref v => Err(self.error(span, FormatError::expected("list", v)))
        }
    }

    fn get_string<'a>(&self, v: &'a Value, span: Span)
            -> Result<&'a str, ExecError> {
        match *v {
            Value::String(ref s) => Ok(s),
            ref v => Err(self.error(span, FormatError::expected("string", v)))
        }
    }

    fn span_one(&self) -> Span {
        Span{lo: self.last_index as BytePos, hi: self.end_index as BytePos}
    }

    fn span_start(&self, start: usize) -> Span {
        Span{lo: start as BytePos, hi: self.end_index as BytePos}
    }
}

fn cur_line_len(s: &str) -> usize {
    let pos = match s.rfind('\n') {
        Some(pos) => pos + 1,
        None => 0,
    };
    s[pos..].chars().count()
}

/// Returns the offset of `child` within `parent`.
fn substr_offset(child: &str, parent: &str) -> usize {
    child.as_ptr() as usize - parent.as_ptr() as usize
}

fn pad_str(buf: &mut String, s: &str, min_col: u32, col_inc: u32,
        min_pad: u32, pad_char: char, left: bool) {
    if min_col == 0 && min_pad == 0 {
        buf.push_str(s);
    } else {
        let pad = min_col.saturating_sub(s.len() as u32);
        let pad = max(min_pad, pad);

        let n = if col_inc > 1 {
            pad + col_inc - (pad % col_inc)
        } else {
            pad
        };

        if left {
            buf.extend(repeat(pad_char).take(n as usize));
            buf.push_str(&s);
        } else {
            buf.push_str(&s);
            buf.extend(repeat(pad_char).take(n as usize));
        }
    }
}

fn make_lowercase(s: &mut String, start: usize) {
    if s[start..].is_ascii() {
        s[start..].make_ascii_lowercase();
    } else {
        let lower = s[start..].to_lowercase();
        s.truncate(start);
        s.push_str(&lower);
    }
}

fn make_uppercase(s: &mut String, start: usize) {
    if s[start..].is_ascii() {
        s[start..].make_ascii_uppercase();
    } else {
        let upper = s[start..].to_uppercase();
        s.truncate(start);
        s.push_str(&upper);
    }
}

fn make_title_case(s: &mut String, mut start: usize) {
    loop {
        let (off, len) = match s[start..].split_whitespace().next() {
            Some(word) => (slice_offset(s, word), word.len()),
            None => break
        };

        make_first_uppercase(s, off);
        start = off + len;
    }
}

fn slice_offset(a: &str, b: &str) -> usize {
    b.as_ptr() as usize - a.as_ptr() as usize
}

fn make_first_uppercase(s: &mut String, start: usize) {
    let (ind, ch) = match s[start..].char_indices()
            .find(|&(_, ch)| !ch.is_whitespace()) {
        Some((ind, ch)) => (ind + start, ch),
        None => return
    };

    if ch.is_ascii() {
        s[ind..=ind].make_ascii_uppercase();
    } else {
        // Removing and inserting is slow, but what alternative do we have?
        let ch = s.remove(ind);
        let mut ind = ind;

        for upper_ch in ch.to_uppercase() {
            s.insert(ind, upper_ch);
            ind += upper_ch.len_utf8();
        }
    }
}

enum Roman {
    One(char, u32),
    Two(char, char, u32),
}

fn get_roman_digit(n: u32, old: bool) -> Roman {
    if old {
        match n {
            n if n >= 1000  => Roman::One('M', 1000),
            500 ..= 999     => Roman::One('D', 500),
            100 ..= 499     => Roman::One('C', 100),
            50 ..= 99       => Roman::One('L', 50),
            10 ..= 49       => Roman::One('X', 10),
            5 ..= 9         => Roman::One('V', 5),
            1 ..= 4         => Roman::One('I', 1),
            _               => panic!("no roman numeral zero")
        }
    } else {
        match n {
            n if n >= 1000  => Roman::One(     'M', 1000),
            900 ..= 999     => Roman::Two('C', 'M', 900),
            500 ..= 899     => Roman::One(     'D', 500),
            400 ..= 499     => Roman::Two('C', 'D', 400),
            100 ..= 399     => Roman::One(     'C', 100),
            90 ..= 99       => Roman::Two('X', 'C', 90),
            50 ..= 89       => Roman::One(     'L', 50),
            40 ..= 49       => Roman::Two('X', 'L', 40),
            10 ..= 39       => Roman::One(     'X', 10),
            9               => Roman::Two('I', 'X', 9),
            5 ..= 8         => Roman::One(     'V', 5),
            4               => Roman::Two('I', 'V', 4),
            1 ..= 3         => Roman::One(     'I', 1),
            _               => panic!("no roman numeral zero")
        }
    }
}

type Cardinal = (&'static str, &'static str);

fn mid_cardinal(n: u32) -> Cardinal {
    MID_CARDINALS[(n - 2) as usize]
}

fn low_cardinal(n: u32) -> Cardinal {
    LOW_CARDINALS[(n - 1) as usize]
}

const MID_CARDINALS: &[Cardinal] = &[
    ("twenty", "twentieth"),
    ("thirty", "thirtieth"),
    ("forty", "fortieth"),
    ("fifty", "fiftieth"),
    ("sixty", "sixtieth"),
    ("seventy", "seventieth"),
    ("eighty", "eightieth"),
    ("ninety", "ninetieth"),
];

const LOW_CARDINALS: &[Cardinal] = &[
    ("one", "first"),
    ("two", "second"),
    ("three", "third"),
    ("four", "fourth"),
    ("five", "fifth"),
    ("six", "sixth"),
    ("seven", "seventh"),
    ("eight", "eighth"),
    ("nine", "ninth"),
    ("ten", "tenth"),
    ("eleven", "eleventh"),
    ("twelve", "twelfth"),
    ("thirteen", "thirteenth"),
    ("fourteen", "fourteenth"),
    ("fifteen", "fifteenth"),
    ("sixteen", "sixteenth"),
    ("seventeen", "seventeenth"),
    ("eighteen", "eighteenth"),
    ("nineteen", "nineteenth"),
];
