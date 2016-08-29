//! Implements decoding Rust values from `Value` instances.
//!
//! See [`value_encode`](../value_encode/index.html) module documentation
//! for details.

use std::slice::Iter;

use serde::{Deserialize, Deserializer};
use serde::de::{self, EnumVisitor, VariantVisitor, Visitor};
use serde::de::value::ValueDeserializer;

use exec::{ExecError, panic};
use error::Error;
use name::Name;
use scope::Scope;
use value::{FromValueRef, Value};

/// Decodes a Rust type from a `Value`.
///
/// See [`value_encode`](../value_encode/index.html) module documentation
/// for details.
pub fn decode_value<T: Deserialize>(scope: &Scope, value: &Value) -> Result<T, Error> {
    let mut de = VDeserializer::new(scope, value);
    let v = try!(T::deserialize(&mut de));
    de.finish();
    Ok(v)
}

impl ::serde::de::Error for ExecError {
    fn custom<T: Into<String>>(msg: T) -> ExecError {
        ExecError::Panic(Some(msg.into().into()))
    }

    fn end_of_stream() -> ExecError {
        ::serde::de::Error::custom("end of stream")
    }
}

struct VDeserializer<'a> {
    scope: &'a Scope,
    state: Vec<DeserializeState<'a>>,
}

#[derive(Debug)]
enum DeserializeState<'a> {
    Value(&'a Value),
    Seq(Iter<'a, Value>),
}

impl<'a> VDeserializer<'a> {
    fn new(scope: &'a Scope, value: &'a Value) -> VDeserializer<'a> {
        VDeserializer{
            scope: scope,
            state: vec![DeserializeState::Value(value)]
        }
    }

    fn finish(&self) {
        if !self.state.is_empty() {
            panic!("state is not empty: {:?}", self.state);
        }
    }

    fn next_value(&mut self) -> Result<&'a Value, ExecError> {
        use self::DeserializeState::*;

        match self.state.pop() {
            None => panic!("missing value state"),
            Some(Value(v)) => Ok(v),
            Some(Seq(mut iter)) => {
                match iter.next() {
                    Some(v) => {
                        self.state.push(Seq(iter));
                        Ok(v)
                    }
                    None => Err(panic("unexpected end of sequence"))
                }
            }
        }
    }

    fn peek_value(&self) -> Result<&'a Value, ExecError> {
        use self::DeserializeState::*;

        match self.state.last() {
            None => panic!("missing value state"),
            Some(&Value(v)) => Ok(v),
            Some(&Seq(ref iter)) => iter.clone().next()
                .ok_or_else(|| panic("unexpected end of sequence"))
        }
    }

    fn read_name(&mut self) -> Result<Name, ExecError> {
        match *try!(self.next_value()) {
            Value::Name(name) => Ok(name),
            ref v => Err(ExecError::expected("name", v))
        }
    }

    fn enter_seq(&mut self) -> Result<usize, ExecError> {
        let v = try!(self.next_value().and_then(<&[Value]>::from_value_ref));
        self.state.push(DeserializeState::Seq(v.iter()));
        Ok(v.len())
    }

    fn leave_seq(&mut self) -> Result<(), ExecError> {
        use self::DeserializeState::*;

        match self.state.pop() {
            None => panic!("missing value state"),
            Some(Value(_)) => panic!("not a sequence"),
            Some(Seq(mut iter)) => {
                match iter.next() {
                    Some(_) => Err(panic("extraneous elements in sequence")),
                    None => Ok(())
                }
            }
        }
    }

    fn enter_enum(&mut self, name: &str) -> Result<(), ExecError> {
        try!(self.enter_seq());
        let name_v = try!(self.read_name());

        self.scope.with_name(name_v, |n| {
            if n != name {
                Err(panic(format!("expected enum `{}`; found `{}`", name, n)))
            } else {
                Ok(())
            }
        })
    }

    fn begin_struct(&mut self, name: &str) -> Result<(), ExecError> {
        try!(self.enter_seq());
        let name_v = try!(self.read_name());

        self.scope.with_name(name_v, |n| {
            if n != name {
                Err(panic(format!("expected struct `{}`; found `{}`", name, n)))
            } else {
                Ok(())
            }
        })
    }

    fn enter_struct(&mut self, name: &str) -> Result<usize, ExecError> {
        try!(self.begin_struct(name));
        self.enter_fields()
    }

    fn enter_tuple_struct(&mut self, name: &str) -> Result<usize, ExecError> {
        try!(self.begin_struct(name));
        self.enter_seq()
    }

    fn enter_fields(&mut self) -> Result<usize, ExecError> {
        let n = try!(self.enter_seq());

        if n % 2 == 1 {
            Err(ExecError::OddKeywordParams)
        } else {
            Ok(n / 2)
        }
    }
}

impl<'a> Deserializer for VDeserializer<'a> {
    type Error = ExecError;

    fn deserialize<V: Visitor>(&mut self, _visitor: V) -> Result<V::Value, ExecError> {
        unimplemented!()
    }

    fn deserialize_bool<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let v = try!(self.next_value().and_then(bool::from_value_ref));
        visitor.visit_bool(v)
    }

    fn deserialize_char<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let v = try!(self.next_value().and_then(char::from_value_ref));
        visitor.visit_char(v)
    }

    fn deserialize_i8<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let v = try!(self.next_value().and_then(i8::from_value_ref));
        visitor.visit_i8(v)
    }

    fn deserialize_i16<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let v = try!(self.next_value().and_then(i16::from_value_ref));
        visitor.visit_i16(v)
    }

    fn deserialize_i32<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let v = try!(self.next_value().and_then(i32::from_value_ref));
        visitor.visit_i32(v)
    }

    fn deserialize_i64<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let v = try!(self.next_value().and_then(i64::from_value_ref));
        visitor.visit_i64(v)
    }

    fn deserialize_isize<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let v = try!(self.next_value().and_then(isize::from_value_ref));
        visitor.visit_isize(v)
    }

    fn deserialize_u8<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let v = try!(self.next_value().and_then(u8::from_value_ref));
        visitor.visit_u8(v)
    }

    fn deserialize_u16<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let v = try!(self.next_value().and_then(u16::from_value_ref));
        visitor.visit_u16(v)
    }

    fn deserialize_u32<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let v = try!(self.next_value().and_then(u32::from_value_ref));
        visitor.visit_u32(v)
    }

    fn deserialize_u64<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let v = try!(self.next_value().and_then(u64::from_value_ref));
        visitor.visit_u64(v)
    }

    fn deserialize_usize<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let v = try!(self.next_value().and_then(usize::from_value_ref));
        visitor.visit_usize(v)
    }

    fn deserialize_f32<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let v = try!(self.next_value().and_then(f64::from_value_ref));
        visitor.visit_f32(v as f32)
    }

    fn deserialize_f64<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let v = try!(self.next_value().and_then(f64::from_value_ref));
        visitor.visit_f64(v)
    }

    fn deserialize_bytes<V: Visitor>(&mut self, visitor: V)
            -> Result<V::Value, ExecError> {
        self.deserialize_seq(visitor)
    }

    fn deserialize_str<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let v = try!(self.next_value().and_then(<&str>::from_value_ref));
        visitor.visit_str(v)
    }

    fn deserialize_string<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let v = try!(self.next_value().and_then(<&str>::from_value_ref));
        visitor.visit_string(v.to_owned())
    }

    fn deserialize_unit<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let _ = try!(self.next_value().and_then(<()>::from_value_ref));
        visitor.visit_unit()
    }

    fn deserialize_option<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        match *try!(self.peek_value()) {
            Value::Unit => {
                let _ = self.next_value();
                visitor.visit_none()
            }
            _ => visitor.visit_some(self)
        }
    }

    fn deserialize_seq<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let n = try!(self.enter_seq());

        visitor.visit_seq(SeqVisitor{
            de: self,
            n: n,
        })
    }

    fn deserialize_tuple<V: Visitor>(&mut self, _len: usize, visitor: V)
            -> Result<V::Value, ExecError> {
        self.deserialize_seq(visitor)
    }

    fn deserialize_seq_fixed_size<V: Visitor>(&mut self, len: usize,
            mut visitor: V) -> Result<V::Value, ExecError> {
        let n = try!(self.enter_seq());

        if n != len {
            return Err(panic(format!(
                "expected list of {} elements; found {}", len, n)));
        }

        visitor.visit_seq(SeqVisitor{
            de: self,
            n: len,
        })
    }

    fn deserialize_map<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        let n = try!(self.enter_seq());

        visitor.visit_map(MapVisitor{
            de: self,
            n: n,
            is_struct: false,
        })
    }

    fn deserialize_newtype_struct<V: Visitor>(&mut self, name: &'static str,
            visitor: V) -> Result<V::Value, ExecError> {
        self.deserialize_tuple_struct(name, 1, visitor)
    }

    fn deserialize_tuple_struct<V: Visitor>(&mut self, name: &'static str,
            _len: usize, mut visitor: V) -> Result<V::Value, ExecError> {
        let n = try!(self.enter_tuple_struct(name));

        let v = try!(visitor.visit_seq(SeqVisitor{
            de: self,
            n: n,
        }));

        try!(self.leave_seq());
        Ok(v)
    }

    fn deserialize_unit_struct<V: Visitor>(&mut self, name: &'static str,
            mut visitor: V) -> Result<V::Value, ExecError> {
        try!(self.begin_struct(name));
        try!(self.next_value().and_then(<()>::from_value_ref));
        try!(self.leave_seq());

        visitor.visit_unit()
    }

    fn deserialize_struct<V: Visitor>(&mut self, name: &'static str,
            _fields: &'static [&'static str], mut visitor: V)
            -> Result<V::Value, ExecError> {
        let n = try!(self.enter_struct(name));

        visitor.visit_map(MapVisitor{
            de: self,
            n: n,
            is_struct: true,
        })
    }

    fn deserialize_struct_field<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        match *try!(self.next_value()) {
            Value::Keyword(name) => {
                self.scope.with_name(name, |name| visitor.visit_str(name))
            }
            ref v => Err(ExecError::expected("keyword", v))
        }
    }

    fn deserialize_enum<V: EnumVisitor>(&mut self, name: &'static str,
            _variants: &'static [&'static str], mut visitor: V)
            -> Result<V::Value, ExecError> {
        try!(self.enter_enum(name));
        visitor.visit(self)
    }

    fn deserialize_ignored_any<V: Visitor>(&mut self, mut visitor: V)
            -> Result<V::Value, ExecError> {
        try!(self.next_value());
        visitor.visit_unit()
    }
}

impl<'a> VariantVisitor for VDeserializer<'a> {
    type Error = ExecError;

    fn visit_variant<V: Deserialize>(&mut self) -> Result<V, ExecError> {
        let name = try!(self.read_name());
        self.scope.with_name(name,
            |name| V::deserialize(&mut name.into_deserializer()))
    }

    fn visit_unit(&mut self) -> Result<(), Self::Error> {
        try!(self.next_value().and_then(<()>::from_value_ref));
        self.leave_seq()
    }

    fn visit_newtype<T: Deserialize>(&mut self) -> Result<T, Self::Error> {
        try!(self.enter_seq());
        let v = try!(T::deserialize(self));
        try!(self.leave_seq());
        try!(self.leave_seq());
        Ok(v)
    }

    fn visit_tuple<V: Visitor>(&mut self, len: usize, visitor: V)
            -> Result<V::Value, Self::Error> {
        let v = try!(self.deserialize_tuple(len, visitor));
        try!(self.leave_seq());
        Ok(v)
    }

    fn visit_struct<V: Visitor>(&mut self, _fields: &'static [&'static str],
            mut visitor: V) -> Result<V::Value, Self::Error> {
        let n = try!(self.enter_fields());

        visitor.visit_map(MapVisitor{
            de: self,
            n: n,
            is_struct: true,
        })
    }
}

struct SeqVisitor<'a, 'b: 'a> {
    de: &'a mut VDeserializer<'b>,
    n: usize,
}

impl<'a, 'b: 'a> de::SeqVisitor for SeqVisitor<'a, 'b> {
    type Error = ExecError;

    fn visit<T: Deserialize>(&mut self) -> Result<Option<T>, ExecError> {
        if self.n == 0 {
            Ok(None)
        } else {
            self.n -= 1;
            let v = try!(T::deserialize(self.de));
            Ok(Some(v))
        }
    }

    fn end(&mut self) -> Result<(), ExecError> {
        self.de.leave_seq()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.n, Some(self.n))
    }
}

struct MapVisitor<'a, 'b: 'a> {
    de: &'a mut VDeserializer<'b>,
    n: usize,
    is_struct: bool,
}

impl<'a, 'b: 'a> de::MapVisitor for MapVisitor<'a, 'b> {
    type Error = ExecError;

    fn visit_key<K: Deserialize>(&mut self) -> Result<Option<K>, ExecError> {
        if self.n == 0 {
            Ok(None)
        } else {
            self.n -= 1;

            if !self.is_struct {
                try!(self.de.enter_seq());
            }

            let k = try!(K::deserialize(self.de));

            Ok(Some(k))
        }
    }

    fn visit_value<V: Deserialize>(&mut self) -> Result<V, ExecError> {
        if self.is_struct {
            V::deserialize(self.de)
        } else {
            let v = try!(V::deserialize(self.de));
            try!(self.de.leave_seq());
            Ok(v)
        }
    }

    fn end(&mut self) -> Result<(), ExecError> {
        if self.is_struct {
            try!(self.de.leave_seq());
        }
        self.de.leave_seq()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.n, Some(self.n))
    }
}
