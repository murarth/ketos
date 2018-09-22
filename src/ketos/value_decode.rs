//! Implements decoding Rust values from `Value` instances.
//!
//! See [`value_encode`](../value_encode/index.html) module documentation
//! for details.

use std::fmt;
use std::slice::Iter;

use serde::de::{
    self, Deserialize, DeserializeSeed, Deserializer, EnumAccess, IntoDeserializer, MapAccess,
    SeqAccess, VariantAccess, Visitor,
};

use error::Error;
use exec::{panic, ExecError};
use name::Name;
use scope::Scope;
use value::{FromValueRef, Value};

/// Decodes a Rust type from a `Value`.
///
/// See [`value_encode`](../value_encode/index.html) module documentation
/// for details.
pub fn decode_value<'de, T: Deserialize<'de>>(
    scope: &'de Scope,
    value: &'de Value,
) -> Result<T, Error> {
    let mut de = VDeserializer::new(scope, value);
    let v = T::deserialize(&mut de)?;
    de.finish();
    Ok(v)
}

impl de::Error for ExecError {
    fn custom<T: fmt::Display>(msg: T) -> ExecError {
        panic(msg.to_string())
    }
}

struct VDeserializer<'de> {
    scope: &'de Scope,
    state: Vec<DeserializeState<'de>>,
}

#[derive(Debug)]
enum DeserializeState<'de> {
    Value(&'de Value),
    Seq(Iter<'de, Value>),
}

impl<'de> VDeserializer<'de> {
    fn new(scope: &'de Scope, value: &'de Value) -> VDeserializer<'de> {
        VDeserializer {
            scope: scope,
            state: vec![DeserializeState::Value(value)],
        }
    }

    fn finish(&self) {
        if !self.state.is_empty() {
            panic!("decode state is not empty: {:?}", self.state);
        }
    }

    fn next_value(&mut self) -> Result<&'de Value, ExecError> {
        use self::DeserializeState::*;

        match self.state.pop() {
            None => panic!("missing value state"),
            Some(Value(v)) => Ok(v),
            Some(Seq(mut iter)) => match iter.next() {
                Some(v) => {
                    self.state.push(Seq(iter));
                    Ok(v)
                }
                None => Err(panic("unexpected end of sequence")),
            },
        }
    }

    fn peek_value(&self) -> Result<&'de Value, ExecError> {
        use self::DeserializeState::*;

        match self.state.last() {
            None => panic!("missing value state"),
            Some(&Value(v)) => Ok(v),
            Some(&Seq(ref iter)) => iter
                .clone()
                .next()
                .ok_or_else(|| panic("unexpected end of sequence")),
        }
    }

    fn read_name(&mut self) -> Result<Name, ExecError> {
        match *self.next_value()? {
            Value::Name(name) => Ok(name),
            ref v => Err(ExecError::expected("name", v)),
        }
    }

    fn enter_seq(&mut self) -> Result<usize, ExecError> {
        let v = self.next_value().and_then(<&[Value]>::from_value_ref)?;
        self.state.push(DeserializeState::Seq(v.iter()));
        Ok(v.len())
    }

    fn leave_seq(&mut self) -> Result<(), ExecError> {
        use self::DeserializeState::*;

        match self.state.pop() {
            None => panic!("missing value state"),
            Some(Value(_)) => panic!("not a sequence"),
            Some(Seq(mut iter)) => match iter.next() {
                Some(_) => Err(panic("extraneous elements in sequence")),
                None => Ok(()),
            },
        }
    }

    fn enter_enum(&mut self, name: &str) -> Result<(), ExecError> {
        self.enter_seq()?;
        let name_v = self.read_name()?;

        self.scope.with_name(name_v, |n| {
            if n != name {
                Err(panic(format!("expected enum `{}`; found `{}`", name, n)))
            } else {
                Ok(())
            }
        })
    }

    fn begin_struct(&mut self, name: &str) -> Result<(), ExecError> {
        self.enter_seq()?;
        let name_v = self.read_name()?;

        self.scope.with_name(name_v, |n| {
            if n != name {
                Err(panic(format!("expected struct `{}`; found `{}`", name, n)))
            } else {
                Ok(())
            }
        })
    }

    fn enter_struct(&mut self, name: &str) -> Result<usize, ExecError> {
        self.begin_struct(name)?;
        self.enter_fields()
    }

    fn enter_tuple_struct(&mut self, name: &str) -> Result<usize, ExecError> {
        self.begin_struct(name)?;
        self.enter_seq()
    }

    fn enter_fields(&mut self) -> Result<usize, ExecError> {
        let n = self.enter_seq()?;

        if n % 2 == 1 {
            Err(ExecError::OddKeywordParams)
        } else {
            Ok(n / 2)
        }
    }
}

impl<'a, 'de: 'a> Deserializer<'de> for &'a mut VDeserializer<'de> {
    type Error = ExecError;

    fn deserialize_any<V: Visitor<'de>>(self, _visitor: V) -> Result<V::Value, ExecError> {
        unimplemented!()
    }

    fn deserialize_bool<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        let v = self.next_value().and_then(bool::from_value_ref)?;
        visitor.visit_bool(v)
    }

    fn deserialize_char<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        let v = self.next_value().and_then(char::from_value_ref)?;
        visitor.visit_char(v)
    }

    fn deserialize_i8<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        let v = self.next_value().and_then(i8::from_value_ref)?;
        visitor.visit_i8(v)
    }

    fn deserialize_i16<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        let v = self.next_value().and_then(i16::from_value_ref)?;
        visitor.visit_i16(v)
    }

    fn deserialize_i32<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        let v = self.next_value().and_then(i32::from_value_ref)?;
        visitor.visit_i32(v)
    }

    fn deserialize_i64<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        let v = self.next_value().and_then(i64::from_value_ref)?;
        visitor.visit_i64(v)
    }

    fn deserialize_u8<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        let v = self.next_value().and_then(u8::from_value_ref)?;
        visitor.visit_u8(v)
    }

    fn deserialize_u16<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        let v = self.next_value().and_then(u16::from_value_ref)?;
        visitor.visit_u16(v)
    }

    fn deserialize_u32<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        let v = self.next_value().and_then(u32::from_value_ref)?;
        visitor.visit_u32(v)
    }

    fn deserialize_u64<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        let v = self.next_value().and_then(u64::from_value_ref)?;
        visitor.visit_u64(v)
    }

    fn deserialize_f32<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        let v = self.next_value().and_then(f64::from_value_ref)?;
        visitor.visit_f32(v as f32)
    }

    fn deserialize_f64<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        let v = self.next_value().and_then(f64::from_value_ref)?;
        visitor.visit_f64(v)
    }

    fn deserialize_bytes<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        self.deserialize_seq(visitor)
    }

    fn deserialize_byte_buf<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        self.deserialize_seq(visitor)
    }

    fn deserialize_str<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        let v = self.next_value().and_then(<&str>::from_value_ref)?;
        visitor.visit_str(v)
    }

    fn deserialize_string<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        let v = self.next_value().and_then(<&str>::from_value_ref)?;
        visitor.visit_string(v.to_owned())
    }

    fn deserialize_unit<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        let _ = self.next_value().and_then(<()>::from_value_ref)?;
        visitor.visit_unit()
    }

    fn deserialize_option<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        match *self.peek_value()? {
            Value::Unit => {
                let _ = self.next_value();
                visitor.visit_none()
            }
            _ => visitor.visit_some(self),
        }
    }

    fn deserialize_seq<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        let n = self.enter_seq()?;

        let v = visitor.visit_seq(SeqVisitor { de: self, n: n })?;

        self.leave_seq()?;
        Ok(v)
    }

    fn deserialize_tuple<V: Visitor<'de>>(
        self,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value, ExecError> {
        self.deserialize_seq(visitor)
    }

    fn deserialize_map<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        let n = self.enter_seq()?;

        let v = visitor.visit_map(MapVisitor {
            de: self,
            n: n,
            is_struct: false,
        })?;

        self.leave_seq()?;
        Ok(v)
    }

    fn deserialize_newtype_struct<V: Visitor<'de>>(
        self,
        name: &'static str,
        visitor: V,
    ) -> Result<V::Value, ExecError> {
        self.deserialize_tuple_struct(name, 1, visitor)
    }

    fn deserialize_tuple_struct<V: Visitor<'de>>(
        self,
        name: &'static str,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value, ExecError> {
        let n = self.enter_tuple_struct(name)?;

        let v = visitor.visit_seq(SeqVisitor { de: self, n: n })?;

        self.leave_seq()?;
        self.leave_seq()?;
        Ok(v)
    }

    fn deserialize_unit_struct<V: Visitor<'de>>(
        self,
        name: &'static str,
        visitor: V,
    ) -> Result<V::Value, ExecError> {
        self.begin_struct(name)?;
        self.next_value().and_then(<()>::from_value_ref)?;
        self.leave_seq()?;

        visitor.visit_unit()
    }

    fn deserialize_struct<V: Visitor<'de>>(
        self,
        name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, ExecError> {
        let n = self.enter_struct(name)?;

        let v = visitor.visit_map(MapVisitor {
            de: self,
            n: n,
            is_struct: true,
        })?;

        self.leave_seq()?;
        self.leave_seq()?;
        Ok(v)
    }

    fn deserialize_identifier<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        match *self.next_value()? {
            Value::Keyword(name) => self.scope.with_name(name, |name| visitor.visit_str(name)),
            ref v => Err(ExecError::expected("keyword", v)),
        }
    }

    fn deserialize_enum<V: Visitor<'de>>(
        self,
        name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, ExecError> {
        self.enter_enum(name)?;
        let v = visitor.visit_enum(&mut *self)?;
        self.leave_seq()?;
        Ok(v)
    }

    fn deserialize_ignored_any<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ExecError> {
        self.next_value()?;
        visitor.visit_unit()
    }
}

impl<'a, 'de: 'a> EnumAccess<'de> for &'a mut VDeserializer<'de> {
    type Error = ExecError;
    type Variant = Self;

    fn variant_seed<V: DeserializeSeed<'de>>(self, seed: V) -> Result<(V::Value, Self), ExecError> {
        let name = self.read_name()?;
        let v = self
            .scope
            .with_name(name, |name| seed.deserialize(name.into_deserializer()))?;

        Ok((v, self))
    }
}

impl<'a, 'de: 'a> VariantAccess<'de> for &'a mut VDeserializer<'de> {
    type Error = ExecError;

    fn unit_variant(self) -> Result<(), Self::Error> {
        self.next_value().and_then(<()>::from_value_ref)
    }

    fn newtype_variant_seed<T: DeserializeSeed<'de>>(
        self,
        seed: T,
    ) -> Result<T::Value, Self::Error> {
        self.enter_seq()?;
        let v = seed.deserialize(&mut *self)?;
        self.leave_seq()?;
        Ok(v)
    }

    fn tuple_variant<V: Visitor<'de>>(
        self,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        let v = self.deserialize_tuple(len, visitor)?;
        Ok(v)
    }

    fn struct_variant<V: Visitor<'de>>(
        self,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        let n = self.enter_fields()?;

        let v = visitor.visit_map(MapVisitor {
            de: self,
            n: n,
            is_struct: true,
        })?;

        self.leave_seq()?;
        Ok(v)
    }
}

struct SeqVisitor<'a, 'de: 'a> {
    de: &'a mut VDeserializer<'de>,
    n: usize,
}

impl<'a, 'de: 'a> SeqAccess<'de> for SeqVisitor<'a, 'de> {
    type Error = ExecError;

    fn next_element_seed<T: DeserializeSeed<'de>>(
        &mut self,
        seed: T,
    ) -> Result<Option<T::Value>, ExecError> {
        if self.n == 0 {
            Ok(None)
        } else {
            self.n -= 1;
            let v = seed.deserialize(&mut *self.de)?;
            Ok(Some(v))
        }
    }

    fn size_hint(&self) -> Option<usize> {
        Some(self.n)
    }
}

struct MapVisitor<'a, 'de: 'a> {
    de: &'a mut VDeserializer<'de>,
    n: usize,
    is_struct: bool,
}

impl<'a, 'de: 'a> MapAccess<'de> for MapVisitor<'a, 'de> {
    type Error = ExecError;

    fn next_key_seed<K: DeserializeSeed<'de>>(
        &mut self,
        seed: K,
    ) -> Result<Option<K::Value>, ExecError> {
        if self.n == 0 {
            Ok(None)
        } else {
            self.n -= 1;

            if !self.is_struct {
                self.de.enter_seq()?;
            }

            let k = seed.deserialize(&mut *self.de)?;

            Ok(Some(k))
        }
    }

    fn next_value_seed<V: DeserializeSeed<'de>>(&mut self, seed: V) -> Result<V::Value, ExecError> {
        if self.is_struct {
            seed.deserialize(&mut *self.de)
        } else {
            let v = seed.deserialize(&mut *self.de)?;
            self.de.leave_seq()?;
            Ok(v)
        }
    }

    fn size_hint(&self) -> Option<usize> {
        Some(self.n)
    }
}
