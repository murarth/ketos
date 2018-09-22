//! Implements encoding and decoding of compiled bytecode file format.

use std::char::from_u32;
use std::fmt;
use std::fs::File;
use std::io::{Cursor, Read, Write};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::str::from_utf8;

use byteorder::{BigEndian, ByteOrder, ReadBytesExt, WriteBytesExt};

use bytecode::{BYTECODE_VERSION, Code};
use bytes::Bytes;
use error::Error;
use exec::Context;
use function::Lambda;
use integer::{Integer, Ratio, Sign};
use io::{IoError, IoMode};
use module::ModuleCode;
use name::{Name, NameDisplay, NameMap, NameSet, NameStore,
    NameInputConversion, NameOutputConversion};
use scope::ImportSet;
use structs::{StructDef, StructValueDef};
use value::Value;

/// First four bytes written to a compiled bytecode file.
pub const MAGIC_NUMBER: &[u8; 4] = b"\0MUR";

/// Error in decoding bytecode file format
#[derive(Debug)]
pub enum DecodeError {
    /// Ratio with zero divisor encountered
    DivisionByZero,
    /// Empty list encountered
    EmptyList,
    /// Incorrect magic number in file header
    IncorrectMagicNumber([u8; 4]),
    /// Incorrect version number in file header
    IncorrectVersion(u32),
    /// Invalid unicode character value
    InvalidChar(u32),
    /// Invalid flags in code object
    InvalidCodeFlags(u32),
    /// Invalid name value
    InvalidName(u32),
    /// Invalid parameter count in code object
    InvalidParamCount,
    /// Invalid type value
    InvalidType(u8),
    /// Invalid UTF-8 in string value
    InvalidUtf8,
    /// Unbalanced `Quasiquote` and `Comma` values
    UnbalancedComma,
    /// Unexpected end-of-file
    UnexpectedEof,
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::DecodeError::*;

        match *self {
            DivisionByZero => f.write_str("zero denominator"),
            EmptyList => f.write_str("empty list"),
            IncorrectMagicNumber(n) => write!(f,
                "incorrect magic number: expected {:?}; found {:?}",
                MAGIC_NUMBER, n),
            IncorrectVersion(n) => write!(f,
                "incorrect version number: expected {:08x}; found {:08x}",
                BYTECODE_VERSION, n),
            InvalidChar(n) => write!(f, "\\u{{{:x}}} is not a valid char", n),
            InvalidCodeFlags(flags) =>
                write!(f, "invalid code object flags: {:#x}", flags),
            InvalidName(n) => write!(f, "invalid name: {}", n),
            InvalidParamCount => f.write_str("invalid parameter count"),
            InvalidType(ty) => write!(f, "invalid type {:#x}", ty),
            InvalidUtf8 => f.write_str("invalid UTF-8 in string"),
            UnbalancedComma => f.write_str("unbalanced quasiquote and comma values"),
            UnexpectedEof => f.write_str("unexpected end-of-file"),
        }
    }
}

impl NameDisplay for DecodeError {
    fn fmt(&self, _names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// Error in encoding bytecode file format
#[derive(Debug)]
pub enum EncodeError {
    /// A `Path` value contains invalid UTF-8
    InvalidUtf8,
    /// Integer overflow in encoding value
    Overflow,
    /// Attempt to encode a type that cannot be encoded
    UnencodableType(&'static str),
    /// Attempt to encode a value that cannot be encoded
    UnencodableValue(&'static str),
}

impl fmt::Display for EncodeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::EncodeError::*;

        match *self {
            InvalidUtf8 => f.write_str("invalid utf-8"),
            Overflow => f.write_str("integer overflow"),
            UnencodableType(ty) => write!(f, "cannot encode value of type `{}`", ty),
            UnencodableValue(v) => write!(f, "cannot encode value {}", v),
        }
    }
}

impl NameDisplay for EncodeError {
    fn fmt(&self, _names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// Read compiled bytecode from a file
pub fn read_bytecode_file(path: &Path, ctx: &Context) -> Result<ModuleCode, Error> {
    let mut f = File::open(path)
        .map_err(|e| IoError::new(IoMode::Open, path, e))?;
    read_bytecode(&mut f, path, ctx)
}

/// Read compiled bytecode
pub fn read_bytecode<R: Read>(r: &mut R, path: &Path, ctx: &Context)
        -> Result<ModuleCode, Error> {
    let mut buf = [0; 4];

    r.read_exact(&mut buf)
        .map_err(|e| IoError::new(IoMode::Read, path, e))?;
    check_magic_number(&buf)?;

    r.read_exact(&mut buf)
        .map_err(|e| IoError::new(IoMode::Read, path, e))?;
    check_version(&buf)?;

    let mut buf = Vec::new();
    r.read_to_end(&mut buf)
        .map_err(|e| IoError::new(IoMode::Read, path, e))?;

    let mut dec = ValueDecoder::new(ctx, &buf);

    let n_names = dec.read_uint()?;
    let mut names = NameInputConversion::new();

    {
        let mut name_store = ctx.scope().names().borrow_mut();

        for _ in 0..n_names {
            let s = dec.read_string()?;
            names.insert(name_store.add(s));
        }
    }

    let n_exports = dec.read_uint()?;
    let mut exports = NameSet::new();

    for _ in 0..n_exports {
        let name = dec.read_name(&names)?;
        exports.insert(name);
    }

    let n_imports = dec.read_uint()?;
    let mut imports = Vec::new();

    for _ in 0..n_imports {
        let mod_name = dec.read_name(&names)?;
        let mut imp = ImportSet::new(mod_name);

        let n_names = dec.read_uint()?;

        for _ in 0..n_names {
            let src = dec.read_name(&names)?;
            let dest = dec.read_name(&names)?;

            imp.names.push((src, dest));
        }

        imports.push(imp);
    }

    let n_consts = dec.read_uint()?;
    let mut consts = Vec::with_capacity(n_consts as usize);

    for _ in 0..n_consts {
        let name = dec.read_name(&names)?;
        let value = dec.read_value(&names)?;
        consts.push((name, value));
    }

    let n_macros = dec.read_uint()?;
    let mut macros = Vec::with_capacity(n_macros as usize);

    for _ in 0..n_macros {
        let name = dec.read_name(&names)?;
        let code = Rc::new(dec.read_code(&names)?);
        macros.push((name, code));
    }

    let n_values = dec.read_uint()?;
    let mut values = Vec::with_capacity(n_values as usize);

    for _ in 0..n_values {
        let name = dec.read_name(&names)?;
        let value = dec.read_value(&names)?;

        values.push((name, value));
    }

    let doc = dec.read_string()?;
    let doc = if doc.is_empty() {
        None
    } else {
        Some(doc.to_owned())
    };

    let n_docs = dec.read_uint()?;
    let mut docs = Vec::with_capacity(n_docs as usize);

    for _ in 0..n_docs {
        let name = dec.read_name(&names)?;
        let doc = dec.read_string()?;

        docs.push((name, doc.to_owned()));
    }

    let mut exprs = Vec::new();

    while !dec.is_empty() {
        exprs.push(Rc::new(dec.read_code(&names)?));
    }

    Ok(ModuleCode{
        code: exprs,
        constants: consts,
        macros: macros,
        values: values,
        exports: exports.into_slice(),
        imports: imports,
        module_doc: doc,
        docs: docs,
    })
}

/// Write compiled bytecode to a file
pub fn write_bytecode_file(path: &Path, module: &ModuleCode,
        name_store: &NameStore) -> Result<(), Error> {
    let mut f = File::create(path)
        .map_err(|e| IoError::new(IoMode::Create, path, e))?;
    write_bytecode(&mut f, path, module, name_store)
}

/// Write compiled bytecode
pub fn write_bytecode<W: Write>(w: &mut W, path: &Path, module: &ModuleCode,
        name_store: &NameStore) -> Result<(), Error> {
    let mut names = NameOutputConversion::new(name_store);
    let mut body_enc = ValueEncoder::new();

    body_enc.write_len(module.imports.len())?;

    for imp in &module.imports {
        body_enc.write_name(imp.module_name, &mut names)?;

        body_enc.write_len(imp.names.len())?;

        for &(src, dest) in &imp.names {
            body_enc.write_name(src, &mut names)?;
            body_enc.write_name(dest, &mut names)?;
        }
    }

    body_enc.write_len(module.constants.len())?;

    for &(name, ref value) in &module.constants {
        body_enc.write_name(name, &mut names)?;
        body_enc.write_value(value, &mut names)?;
    }

    body_enc.write_len(module.macros.len())?;

    for &(name, ref mac) in &module.macros {
        body_enc.write_name(name, &mut names)?;
        body_enc.write_code(mac, &mut names)?;
    }

    body_enc.write_len(module.values.len())?;

    for &(name, ref value) in &module.values {
        body_enc.write_name(name, &mut names)?;
        body_enc.write_value(value, &mut names)?;
    }

    if let Some(ref doc) = module.module_doc {
        body_enc.write_string(doc)?;
    } else {
        body_enc.write_string("")?;
    }

    body_enc.write_len(module.docs.len())?;

    for &(name, ref doc) in &module.docs {
        body_enc.write_name(name, &mut names)?;
        body_enc.write_string(doc)?;
    }

    for code in &module.code {
        body_enc.write_code(code, &mut names)?;
    }

    let mut head_enc = ValueEncoder::new();

    head_enc.write_len(names.len())?;

    for name in names.names() {
        head_enc.write_string(name)?;
    }

    head_enc.write_len(module.exports.len())?;

    for name in &module.exports {
        head_enc.write_name(name, &mut names)?;
    }

    w.write_all(MAGIC_NUMBER)
        .map_err(|e| IoError::new(IoMode::Write, path, e))?;

    w.write_u32::<BigEndian>(BYTECODE_VERSION)
        .map_err(|e| IoError::new(IoMode::Write, path, e))?;

    w.write_all(&head_enc.into_bytes())
        .and_then(|_| w.write_all(&body_enc.into_bytes()))
        .map_err(|e| IoError::new(IoMode::Write, path, e))?;

    Ok(())
}

fn check_magic_number(num: &[u8; 4]) -> Result<(), DecodeError> {
    if num == MAGIC_NUMBER {
        Ok(())
    } else {
        Err(DecodeError::IncorrectMagicNumber(*num))
    }
}

fn check_version(num: &[u8; 4]) -> Result<(), DecodeError> {
    let version = BigEndian::read_u32(num);

    if version == BYTECODE_VERSION {
        Ok(())
    } else {
        Err(DecodeError::IncorrectVersion(version))
    }
}

/// Reads values from a byte stream
struct ValueDecoder<'a, 'data> {
    data: Cursor<&'data [u8]>,
    ctx: &'a Context,
}

impl<'a, 'data> ValueDecoder<'a, 'data> {
    /// Creates a new `ValueDecoder` reading from the given byte stream.
    /// `ctx` is the execution context whose module-level scope
    /// will be passed to newly created `Lambda` objects.
    fn new(ctx: &'a Context, data: &'data [u8]) -> ValueDecoder<'a, 'data> {
        ValueDecoder{
            data: Cursor::new(data),
            ctx: ctx,
        }
    }

    /// Returns `true` if there is no data left to decode.
    fn is_empty(&self) -> bool {
        let buf = self.data.get_ref();
        self.data.position() as usize == buf.len()
    }

    /// Reads a `Value` from the byte stream.
    fn read_value(&mut self, names: &NameInputConversion) -> Result<Value, DecodeError> {
        use self::types::*;

        let ty = self.read_u8()?;

        match ty {
            UNIT => Ok(Value::Unit),
            BOOL_TRUE => Ok(Value::Bool(true)),
            BOOL_FALSE => Ok(Value::Bool(false)),
            FLOAT => Ok(Value::Float(self.read_f64()?)),
            INTEGER | INTEGER_NEG => {
                let sign = if ty == INTEGER {
                    Sign::Plus
                } else {
                    Sign::Minus
                };

                self.read_integer(sign).map(Value::Integer)
            }
            INTEGER_ZERO => Ok(Value::Integer(Integer::zero())),
            RATIO | RATIO_NEG => {
                let sign = if ty == RATIO {
                    Sign::Plus
                } else {
                    Sign::Minus
                };

                let numer = self.read_integer(sign)?;
                // Denominator is always positive
                let denom = self.read_integer(Sign::Plus)?;

                if denom.is_zero() {
                    Err(DecodeError::DivisionByZero)
                } else {
                    Ok(Ratio::new(numer, denom).into())
                }
            }
            RATIO_ZERO => Ok(Value::Ratio(Ratio::zero())),
            NAME => Ok(Value::Name(self.read_name(names)?)),
            KEYWORD => Ok(Value::Keyword(self.read_name(names)?)),
            CHAR => {
                let c = self.read_u32()?;
                from_u32(c)
                    .map(Value::Char)
                    .ok_or_else(|| DecodeError::InvalidChar(c))
            }
            STRING => self.read_string().map(|s| s.into()),
            BYTES => self.read_byte_string().map(|s| s.into()),
            PATH => self.read_string().map(|s| PathBuf::from(s).into()),
            // XXX: Decoding struct values is not implemented
            STRUCT => Err(DecodeError::InvalidType(STRUCT)),
            STRUCT_DEF => {
                let name = self.read_name(names)?;
                let n = self.read_uint()?;
                let mut fields = NameMap::new();

                for _ in 0..n {
                    let field = self.read_name(names)?;
                    let ty = self.read_name(names)?;

                    fields.insert(field, ty);
                }

                let def = StructValueDef::new(fields.into_slice());

                Ok(Value::StructDef(Rc::new(StructDef::new(name, Box::new(def)))))
            }
            QUASI_QUOTE => {
                let n = self.read_u8()? as u32;
                self.read_value(names).map(|v| v.quasiquote(n))
            }
            QUASI_QUOTE_ONE => self.read_value(names).map(|v| v.quasiquote(1)),
            COMMA => {
                let n = self.read_u8()? as u32;
                self.read_value(names).map(|v| v.comma(n))
            }
            COMMA_ONE => self.read_value(names).map(|v| v.comma(1)),
            COMMA_AT => {
                let n = self.read_u8()? as u32;
                self.read_value(names).map(|v| v.comma_at(n))
            }
            COMMA_AT_ONE => self.read_value(names).map(|v| v.comma_at(1)),
            QUOTE => {
                let n = self.read_u8()? as u32;
                self.read_value(names).map(|v| v.quote(n))
            }
            QUOTE_ONE => self.read_value(names).map(|v| v.quote(1)),
            LIST => {
                let n = self.read_len()?;

                if n == 0 {
                    return Err(DecodeError::EmptyList);
                }

                let mut v = Vec::with_capacity(n);

                for _ in 0..n {
                    v.push(self.read_value(names)?);
                }

                Ok(v.into())
            }
            LAMBDA => {
                let code = self.read_code(names)?;
                Ok(Value::Lambda(Lambda::new(Rc::new(code), self.ctx.scope())))
            }
            _ => Err(DecodeError::InvalidType(ty))
        }
    }

    fn read_bytes(&mut self, n: usize) -> Result<&'data [u8], DecodeError> {
        read_cursor(&mut self.data, n).ok_or(DecodeError::UnexpectedEof)
    }

    fn read_code(&mut self, names: &NameInputConversion) -> Result<Code, DecodeError> {
        use bytecode::code_flags::*;

        let flags = self.read_u8()? as u32;

        if flags & ALL_FLAGS != flags {
            return Err(DecodeError::InvalidCodeFlags(flags));
        }

        let name = if flags & HAS_NAME == 0 {
            None
        } else {
            Some(self.read_name(names)?)
        };

        let doc = if flags & HAS_DOC_STRING == 0 {
            None
        } else {
            Some(self.read_string()?.to_owned())
        };

        let n_consts = self.read_len()?;
        let mut consts = Vec::with_capacity(n_consts);

        for _ in 0..n_consts {
            let v = self.read_value(names)?;
            validate_value(&v)?;
            consts.push(v);
        }

        let code_bytes = self.read_len()?;
        let code = self.read_bytes(code_bytes)?.to_vec();

        let n_params = self.read_uint()?;
        let req_params = self.read_uint()?;

        if n_params < req_params {
            return Err(DecodeError::InvalidParamCount);
        }

        let mut kw_params = Vec::new();

        match flags & PARAM_FLAGS_MASK {
            0 | HAS_REST_PARAMS => (),
            HAS_KW_PARAMS => {
                let n = self.read_len()?;

                if n == 0 {
                    return Err(DecodeError::InvalidCodeFlags(flags));
                }

                kw_params.reserve_exact(n);

                for _ in 0..n {
                    kw_params.push(self.read_name(names)?);
                }
            }
            _ => return Err(DecodeError::InvalidCodeFlags(flags))
        }

        Ok(Code{
            name: name,
            consts: consts.into_boxed_slice(),
            code: code.into_boxed_slice(),
            kw_params: kw_params.into_boxed_slice(),
            n_params: n_params,
            req_params: req_params,
            flags: flags,
            doc: doc,
        })
    }

    fn read_name(&mut self, names: &NameInputConversion) -> Result<Name, DecodeError> {
        let n = self.read_uint()?;
        names.get(n).ok_or_else(|| DecodeError::InvalidName(n))
    }

    fn read_string(&mut self) -> Result<&'data str, DecodeError> {
        let n = self.read_uint()?;
        let b = self.read_bytes(n as usize)?;

        from_utf8(b).map_err(|_| DecodeError::InvalidUtf8)
    }

    fn read_byte_string(&mut self) -> Result<Bytes, DecodeError> {
        let n = self.read_uint()?;
        let b = self.read_bytes(n as usize)?;

        Ok(Bytes::from(b))
    }

    fn read_integer(&mut self, sign: Sign) -> Result<Integer, DecodeError> {
        let n = self.read_uint()?;
        let b = self.read_bytes(n as usize)?;
        Ok(Integer::from_bytes_be(sign, b))
    }

    fn read_u8(&mut self) -> Result<u8, DecodeError> {
        Ok(self.data.read_u8()
            .map_err(|_| DecodeError::UnexpectedEof)?)
    }

    fn read_u32(&mut self) -> Result<u32, DecodeError> {
        Ok(self.data.read_u32::<BigEndian>()
            .map_err(|_| DecodeError::UnexpectedEof)?)
    }

    fn read_len(&mut self) -> Result<usize, DecodeError> {
        self.read_uint().map(|n| n as usize)
    }

    fn read_uint(&mut self) -> Result<u32, DecodeError> {
        let hi = self.read_u8()? as u32;

        if hi & 0x80 == 0 {
            Ok(hi)
        } else {
            let hi = (hi & 0x7f) << 8;
            let lo = self.read_u8()? as u32;
            Ok(hi | lo)
        }
    }

    fn read_f64(&mut self) -> Result<f64, DecodeError> {
        Ok(self.data.read_f64::<BigEndian>()
            .map_err(|_| DecodeError::UnexpectedEof)?)
    }
}

fn validate_value(v: &Value) -> Result<(), DecodeError> {
    validate_value_inner(v, 0)
}

fn validate_value_inner(v: &Value, quasi: u32) -> Result<(), DecodeError> {
    match *v {
        Value::Quasiquote(ref v, n) => validate_value_inner(v, quasi + n),
        Value::Comma(ref v, n) | Value::CommaAt(ref v, n) => if n >= quasi {
            Err(DecodeError::UnbalancedComma)
        } else {
            validate_value_inner(v, quasi - n)
        },
        Value::Quote(ref v, _) => validate_value_inner(v, quasi),
        _ => Ok(())
    }
}

/// Encodes values to a byte stream
struct ValueEncoder {
    data: Vec<u8>,
}

impl ValueEncoder {
    /// Creates a new `ValueEncoder`.
    fn new() -> ValueEncoder {
        ValueEncoder{
            data: Vec::with_capacity(32),
        }
    }

    /// Consumes the encoder and returns the encoded byte stream.
    fn into_bytes(self) -> Vec<u8> {
        self.data
    }

    /// Writes a `Value` to the byte stream.
    fn write_value(&mut self, value: &Value, names: &mut NameOutputConversion) -> Result<(), EncodeError> {
        use self::types::*;

        match *value {
            Value::Unit => self.write_u8(UNIT),
            Value::Bool(b) => if b {
                self.write_u8(BOOL_TRUE);
            } else {
                self.write_u8(BOOL_FALSE);
            },
            Value::Float(f) => {
                self.write_u8(FLOAT);
                self.write_f64(f);
            }
            Value::Integer(ref i) => {
                if i.is_zero() {
                    self.write_u8(INTEGER_ZERO);
                } else {
                    if i.is_negative() {
                        self.write_u8(INTEGER_NEG);
                    } else {
                        self.write_u8(INTEGER);
                    }

                    self.write_integer(i)?;
                }
            }
            Value::Ratio(ref r) => {
                if r.is_zero() {
                    self.write_u8(RATIO_ZERO);
                } else {
                    if r.is_positive() {
                        self.write_u8(RATIO);
                    } else {
                        self.write_u8(RATIO_NEG);
                    }

                    self.write_integer(r.numer())?;
                    self.write_integer(r.denom())?;
                }
            }
            Value::Name(name) => {
                self.write_u8(NAME);
                self.write_name(name, names)?;
            }
            Value::Keyword(name) => {
                self.write_u8(KEYWORD);
                self.write_name(name, names)?;
            }
            Value::Char(c) => {
                self.write_u8(CHAR);
                self.write_u32(c as u32);
            }
            Value::String(ref s) => {
                self.write_u8(STRING);
                self.write_string(s)?;
            }
            Value::Bytes(ref s) => {
                self.write_u8(BYTES);
                self.write_byte_string(s)?;
            }
            Value::Path(ref p) => {
                self.write_u8(PATH);
                self.write_path(p)?;
            }
            // TODO: Encode/decode struct values.
            // Modules could begin with a listing of all defined StructDefs,
            // which could be referenced by index thereafter.
            // However, Struct encoding/decoding must also account for the
            // possibility that a Struct value exists in a module based on a
            // definition which is found in another module.
            Value::Struct(_) => return Err(EncodeError::UnencodableType("struct")),
            Value::StructDef(ref def) => {
                if let Some(vdef) = def.def().downcast_ref::<StructValueDef>() {
                    self.write_u8(STRUCT_DEF);

                    let fields = vdef.fields();

                    self.write_name(def.name(), names)?;
                    self.write_len(fields.len())?;

                    for &(name, ty) in fields {
                        self.write_name(name, names)?;
                        self.write_name(ty, names)?;
                    }
                } else {
                    return Err(EncodeError::UnencodableType("struct-def"));
                }
            }
            Value::Quasiquote(ref v, 1) => {
                self.write_u8(QUASI_QUOTE_ONE);
                self.write_value(v, names)?;
            }
            Value::Quasiquote(ref v, n) if n <= 0xff => {
                self.write_u8(QUASI_QUOTE);
                self.write_u8(n as u8);
                self.write_value(v, names)?;
            }
            Value::Comma(ref v, 1) => {
                self.write_u8(COMMA_ONE);
                self.write_value(v, names)?;
            }
            Value::Comma(ref v, n) if n <= 0xff => {
                self.write_u8(COMMA);
                self.write_u8(n as u8);
                self.write_value(v, names)?;
            }
            Value::CommaAt(ref v, 1) => {
                self.write_u8(COMMA_AT_ONE);
                self.write_value(v, names)?;
            }
            Value::CommaAt(ref v, n) if n <= 0xff => {
                self.write_u8(COMMA_AT);
                self.write_u8(n as u8);
                self.write_value(v, names)?;
            }
            Value::Quote(ref v, 1) => {
                self.write_u8(QUOTE_ONE);
                self.write_value(v, names)?;
            }
            Value::Quote(ref v, n) if n <= 0xff => {
                self.write_u8(QUOTE);
                self.write_u8(n as u8);
                self.write_value(v, names)?;
            }
            Value::Comma(_, _)
            | Value::CommaAt(_, _)
            | Value::Quasiquote(_, _)
            | Value::Quote(_, _) => {
                return Err(EncodeError::Overflow);
            }
            Value::List(ref li) => {
                self.write_u8(LIST);
                self.write_len(li.len())?;

                for v in li {
                    self.write_value(v, names)?;
                }
            }
            Value::Lambda(ref l) => {
                if l.values.is_some() {
                    return Err(EncodeError::UnencodableValue(
                        "lambda with enclosed values"));
                }
                self.write_u8(LAMBDA);
                self.write_code(&l.code, names)?;
            }
            Value::Foreign(_) =>
                return Err(EncodeError::UnencodableType("foreign value")),
            ref v => return Err(EncodeError::UnencodableType(v.type_name()))
        }

        Ok(())
    }

    fn write_bytes(&mut self, b: &[u8]) {
        self.data.extend(b);
    }

    fn write_code(&mut self, code: &Code, names: &mut NameOutputConversion) -> Result<(), EncodeError> {
        use bytecode::code_flags::*;

        self.write_u8(code.flags as u8);

        assert_eq!(code.flags & HAS_NAME != 0, code.name.is_some());
        assert_eq!(code.flags & HAS_DOC_STRING != 0, code.doc.is_some());

        if let Some(name) = code.name {
            self.write_name(name, names)?;
        }

        if let Some(ref doc) = code.doc {
            self.write_string(doc)?;
        }

        self.write_len(code.consts.len())?;

        for c in code.consts.iter() {
            self.write_value(c, names)?;
        }

        self.write_len(code.code.len())?;
        self.write_bytes(&code.code);

        self.write_uint(code.n_params)?;
        self.write_uint(code.req_params)?;

        assert_eq!(code.flags & PARAM_FLAGS_MASK == HAS_KW_PARAMS,
            !code.kw_params.is_empty());

        if !code.kw_params.is_empty() {
            self.write_len(code.kw_params.len())?;

            for &name in code.kw_params.iter() {
                self.write_name(name, names)?;
            }
        }

        Ok(())
    }

    fn write_integer(&mut self, i: &Integer) -> Result<(), EncodeError> {
        let (_, b) = i.to_bytes_be();

        self.write_len(b.len())?;
        self.write_bytes(&b);
        Ok(())
    }

    fn write_name(&mut self, name: Name, names: &mut NameOutputConversion) -> Result<(), EncodeError> {
        let n = names.add(name);
        self.write_uint(n)
    }

    fn write_string(&mut self, s: &str) -> Result<(), EncodeError> {
        self.write_len(s.len())?;
        self.write_bytes(s.as_bytes());
        Ok(())
    }

    fn write_byte_string(&mut self, b: &[u8]) -> Result<(), EncodeError> {
        self.write_len(b.len())?;
        self.write_bytes(b);
        Ok(())
    }

    fn write_path(&mut self, p: &Path) -> Result<(), EncodeError> {
        match p.to_str() {
            Some(s) => self.write_string(s),
            None => Err(EncodeError::InvalidUtf8)
        }
    }

    fn write_u8(&mut self, b: u8) {
        self.data.push(b);
    }

    fn write_u32(&mut self, n: u32) {
        let _ = self.data.write_u32::<BigEndian>(n);
    }

    fn write_len(&mut self, n: usize) -> Result<(), EncodeError> {
        if n > 0x7fff {
            Err(EncodeError::Overflow)
        } else {
            self.write_uint(n as u32)
        }
    }

    fn write_uint(&mut self, n: u32) -> Result<(), EncodeError> {
        if n <= 0x7f {
            self.write_u8(n as u8);
            Ok(())
        } else if n <= 0x7fff {
            let hi = (n >> 8) as u8;
            let lo = n as u8;
            self.write_u8(hi | 0x80);
            self.write_u8(lo);
            Ok(())
        } else {
            Err(EncodeError::Overflow)
        }
    }

    fn write_f64(&mut self, f: f64) {
        let _ = self.data.write_f64::<BigEndian>(f);
    }
}

/// Reads bytes from a cursor without copying data.
fn read_cursor<'a>(cur: &mut Cursor<&'a [u8]>, n: usize) -> Option<&'a [u8]> {
    let pos = cur.position() as usize;
    let bytes = *cur.get_ref();

    if bytes.len() < pos + n {
        None
    } else {
        cur.set_position((pos + n) as u64);
        Some(&bytes[pos..pos + n])
    }
}

macro_rules! types {
    ( $( $name:ident = $value:expr , )+ ) => {
        /// Byte constants indicating the type of the following value.
        ///
        /// Any addition, deletion, or modification to these constants constitutes
        /// a breaking change to the bytecode format.
        mod types {
            $( pub const $name: u8 = $value; )+
        }
    }
}

types!{
    UNIT = 0,
    BOOL_TRUE = 1,
    BOOL_FALSE = 2,
    FLOAT = 3,
    INTEGER = 4,
    INTEGER_NEG = 5,
    INTEGER_ZERO = 6,
    RATIO = 7,
    RATIO_NEG = 8,
    RATIO_ZERO = 9,
    NAME = 10,
    KEYWORD = 11,
    CHAR = 12,
    STRING = 13,
    BYTES = 14,
    PATH = 15,
    STRUCT = 16,
    STRUCT_DEF = 17,
    QUASI_QUOTE = 18,
    QUASI_QUOTE_ONE = 19,
    COMMA = 20,
    COMMA_ONE = 21,
    COMMA_AT = 22,
    COMMA_AT_ONE = 23,
    QUOTE = 24,
    QUOTE_ONE = 25,
    LIST = 26,
    LAMBDA = 27,
}
