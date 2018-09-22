//! Implements encoding Rust values into `Value` instances.
//!
//! Encoding and decoding is performed using the `Serialize`/`Deserialize`
//! traits of the [`serde`](https://github.com/serde-rs/serde) crate.
//!
//! `struct` values are encoded as a list of two elements: the `struct` name
//! followed by a series of fields. Tuple structs contain an ordered list of
//! values, while traditional structs contain a list of inline `:key value` pairs.
//!
//! For example, given a `struct` definition such as:
//!
//! ```ignore
//! #[derive(Debug, Deserialize, Serialize)]
//! struct MyStruct {
//!     a: i32,
//!     b: Vec<i32>,
//! }
//! ```
//!
//! The value `MyStruct{a: 1, b: vec![2, 3, 4]}` would be encoded as
//! `(MyStruct (:a 1 :b (2 3 4)))`.
//!
//! Similarly, `enum` values are encoded as a list of three elements:
//! the `enum` name, the variant name, and a list of any values contained
//! in the variant.

use std::fmt;

use serde::ser::{self, Serialize, Serializer};

use error::Error;
use exec::{panic, ExecError};
use name::Name;
use scope::Scope;
use value::Value;

/// Encodes a Rust type into a `Value`.
///
/// See [`value_encode`](index.html) module documentation for details.
pub fn encode_value<T: Serialize>(scope: &Scope, value: &T) -> Result<Value, Error> {
    let mut ser = VSerializer::new(scope);
    value.serialize(&mut ser)?;
    Ok(ser.value.expect("empty serializer"))
}

impl ser::Error for ExecError {
    fn custom<T: fmt::Display>(msg: T) -> ExecError {
        panic(msg.to_string())
    }
}

struct VSerializer<'a> {
    scope: &'a Scope,
    value: Option<Value>,
    state: Vec<SerializeState>,
}

struct SubSerializer<'a, 'b: 'a>(&'a mut VSerializer<'b>);

enum SerializeState {
    /// Enum value opened; waiting for variant name
    BeginEnum(Name),
    /// Sequence opened
    Sequence(Vec<Value>),
    /// Struct field sequence opened; expecting key
    StructKey(Vec<Value>),
    /// Struct field sequence opened; expecting value
    StructValue(Vec<Value>),
    /// Mapping key-value or struct name-value pair opened; waiting for key
    MapKey,
    /// Mapping key-value or struct name-value pair opened; waiting for value
    MapValue(Value),
}

impl<'a> VSerializer<'a> {
    fn new(scope: &Scope) -> VSerializer {
        VSerializer {
            scope: scope,
            value: None,
            state: Vec::new(),
        }
    }

    fn emit_value<T: Into<Value>>(&mut self, value: T) {
        use self::SerializeState::*;

        let value = value.into();

        match self.state.pop() {
            None => self.value = Some(value),
            Some(BeginEnum(_)) => panic!("missing enum variant"),
            Some(Sequence(mut v)) => {
                v.push(value);
                self.state.push(Sequence(v));
            }
            Some(StructKey(mut v)) => {
                v.push(value);
                self.state.push(StructValue(v));
            }
            Some(StructValue(mut v)) => {
                v.push(value);
                self.state.push(StructKey(v));
            }
            Some(MapKey) => {
                self.state.push(MapValue(value));
            }
            Some(MapValue(k)) => {
                self.emit_value(vec![k, value]);
            }
        }
    }

    fn emit_str(&mut self, s: &str) {
        if self.expect_field() {
            self.field_name(s);
        } else {
            self.emit_value(s);
        }
    }

    fn expect_field(&self) -> bool {
        match self.state.last() {
            Some(&SerializeState::StructKey(_)) => true,
            _ => false,
        }
    }

    fn begin_enum(&mut self, name: &str) {
        let name = self.get_name(name);
        self.state.push(SerializeState::BeginEnum(name));
    }

    fn end_enum(&mut self) {
        self.end_seq();
        self.end_seq();
    }

    fn enum_variant(&mut self, variant: &str, len: usize) {
        match self.state.pop().unwrap() {
            SerializeState::BeginEnum(name) => {
                let variant = self.get_name(variant);
                let mut v = Vec::with_capacity(3);

                v.push(Value::Name(name));
                v.push(Value::Name(variant));

                self.state.push(SerializeState::Sequence(v));
                self.state
                    .push(SerializeState::Sequence(Vec::with_capacity(len)));
            }
            _ => panic!("missing begin_enum"),
        }
    }

    fn struct_variant(&mut self, variant: &str, len: usize) {
        match self.state.pop().unwrap() {
            SerializeState::BeginEnum(name) => {
                let variant = self.get_name(variant);
                let mut v = Vec::with_capacity(3);

                v.push(Value::Name(name));
                v.push(Value::Name(variant));

                self.state.push(SerializeState::Sequence(v));
                self.state
                    .push(SerializeState::StructKey(Vec::with_capacity(len * 2)));
            }
            _ => panic!("missing begin_enum"),
        }
    }

    fn field_name(&mut self, f_name: &str) {
        let name = self.get_name(f_name);
        self.emit_value(Value::Keyword(name));
    }

    fn begin_struct(&mut self, name: &str, len: usize) {
        let name = self.get_name(name);
        let mut v = Vec::with_capacity(2);
        v.push(Value::Name(name));

        self.state.push(SerializeState::Sequence(v));
        self.state
            .push(SerializeState::StructKey(Vec::with_capacity(len * 2)));
    }

    fn end_struct(&mut self) {
        match self.state.pop().unwrap() {
            SerializeState::StructKey(v) => {
                self.emit_value(v);
            }
            _ => panic!("missing struct state"),
        }
        self.end_seq();
    }

    fn emit_unit_struct(&mut self, name: &str) {
        let name = self.get_name(name);
        self.emit_value(vec![Value::Name(name), ().into()]);
    }

    fn emit_unit_variant(&mut self, name: &str, variant: &str) {
        let name = self.get_name(name);
        let variant = self.get_name(variant);

        self.emit_value(vec![Value::Name(name), Value::Name(variant), ().into()]);
    }

    fn begin_tuple_struct(&mut self, name: &str, len: usize) {
        let name = self.get_name(name);
        let mut v = Vec::with_capacity(2);
        v.push(Value::Name(name));

        self.state.push(SerializeState::Sequence(v));
        self.state
            .push(SerializeState::Sequence(Vec::with_capacity(len)));
    }

    // For now, Option values are encoded as:
    //  None    => ()
    //  Some(v) => v
    fn emit_none(&mut self) {
        self.emit_value(());
    }

    fn begin_seq(&mut self, len: usize) {
        self.state
            .push(SerializeState::Sequence(Vec::with_capacity(len)));
    }

    fn end_seq(&mut self) {
        match self.state.pop().expect("not in sequence") {
            SerializeState::Sequence(v) => {
                self.emit_value(v);
            }
            _ => panic!("missing sequence"),
        }
    }

    fn emit_map_key(&mut self) {
        if !self.expect_field() {
            self.state.push(SerializeState::MapKey);
        }
    }

    fn get_name(&mut self, name: &str) -> Name {
        self.scope.add_name(name)
    }
}

impl<'a, 'b: 'a> Serializer for &'a mut VSerializer<'b> {
    type Ok = ();
    type Error = ExecError;

    type SerializeSeq = SubSerializer<'a, 'b>;
    type SerializeTuple = SubSerializer<'a, 'b>;
    type SerializeTupleStruct = SubSerializer<'a, 'b>;
    type SerializeTupleVariant = SubSerializer<'a, 'b>;
    type SerializeMap = SubSerializer<'a, 'b>;
    type SerializeStruct = SubSerializer<'a, 'b>;
    type SerializeStructVariant = SubSerializer<'a, 'b>;

    fn serialize_bool(self, v: bool) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_char(self, v: char) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_i8(self, v: i8) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_i16(self, v: i16) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_i32(self, v: i32) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_i64(self, v: i64) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_u8(self, v: u8) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_u16(self, v: u16) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_u32(self, v: u32) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_u64(self, v: u64) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_f32(self, v: f32) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_f64(self, v: f64) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_str(self, v: &str) -> Result<(), ExecError> {
        self.emit_str(v);
        Ok(())
    }

    fn serialize_bytes(self, v: &[u8]) -> Result<(), ExecError> {
        use serde::ser::SerializeSeq;

        let mut ser = self.serialize_seq(Some(v.len()))?;

        for b in v {
            ser.serialize_element(b)?;
        }

        ser.end()
    }

    fn serialize_unit(self) -> Result<(), ExecError> {
        self.emit_value(());
        Ok(())
    }

    fn serialize_unit_struct(self, name: &'static str) -> Result<(), ExecError> {
        self.emit_unit_struct(name);
        Ok(())
    }

    fn serialize_unit_variant(
        self,
        name: &'static str,
        _index: u32,
        variant: &'static str,
    ) -> Result<(), ExecError> {
        self.emit_unit_variant(name, variant);
        Ok(())
    }

    fn serialize_none(self) -> Result<(), ExecError> {
        self.emit_none();
        Ok(())
    }

    fn serialize_some<V: ?Sized + Serialize>(self, value: &V) -> Result<(), ExecError> {
        value.serialize(self)
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<SubSerializer<'a, 'b>, ExecError> {
        self.begin_seq(len.unwrap_or(0));
        Ok(SubSerializer(self))
    }

    fn serialize_tuple(self, len: usize) -> Result<SubSerializer<'a, 'b>, ExecError> {
        self.serialize_seq(Some(len))
    }

    fn serialize_map(self, len: Option<usize>) -> Result<SubSerializer<'a, 'b>, ExecError> {
        self.serialize_seq(len)
    }

    fn serialize_struct(
        self,
        name: &'static str,
        len: usize,
    ) -> Result<SubSerializer<'a, 'b>, ExecError> {
        self.begin_struct(name, len);
        Ok(SubSerializer(self))
    }

    fn serialize_newtype_struct<T: ?Sized + Serialize>(
        self,
        name: &'static str,
        value: &T,
    ) -> Result<(), ExecError> {
        use serde::ser::SerializeTupleStruct;

        let mut ser = self.serialize_tuple_struct(name, 1)?;

        ser.serialize_field(value)?;
        ser.end()
    }

    fn serialize_tuple_struct(
        self,
        name: &'static str,
        len: usize,
    ) -> Result<SubSerializer<'a, 'b>, ExecError> {
        self.begin_tuple_struct(name, len);
        Ok(SubSerializer(self))
    }

    fn serialize_newtype_variant<T: ?Sized + Serialize>(
        self,
        name: &'static str,
        index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<(), ExecError> {
        use serde::ser::SerializeTupleVariant;

        let mut ser = self.serialize_tuple_variant(name, index, variant, 1)?;

        ser.serialize_field(value)?;
        ser.end()
    }

    fn serialize_tuple_variant(
        self,
        name: &'static str,
        _index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<SubSerializer<'a, 'b>, ExecError> {
        self.begin_enum(name);
        self.enum_variant(variant, len);
        Ok(SubSerializer(self))
    }

    fn serialize_struct_variant(
        self,
        name: &'static str,
        _index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<SubSerializer<'a, 'b>, ExecError> {
        self.begin_enum(name);
        self.struct_variant(variant, len);
        Ok(SubSerializer(self))
    }
}

impl<'a, 'b: 'a> ser::SerializeSeq for SubSerializer<'a, 'b> {
    type Ok = ();
    type Error = ExecError;

    fn serialize_element<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), ExecError> {
        value.serialize(&mut *self.0)
    }

    fn end(self) -> Result<(), ExecError> {
        self.0.end_seq();
        Ok(())
    }
}

impl<'a, 'b: 'a> ser::SerializeTuple for SubSerializer<'a, 'b> {
    type Ok = ();
    type Error = ExecError;

    fn serialize_element<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), ExecError> {
        value.serialize(&mut *self.0)
    }

    fn end(self) -> Result<(), ExecError> {
        self.0.end_seq();
        Ok(())
    }
}

impl<'a, 'b: 'a> ser::SerializeTupleStruct for SubSerializer<'a, 'b> {
    type Ok = ();
    type Error = ExecError;

    fn serialize_field<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), ExecError> {
        value.serialize(&mut *self.0)
    }

    fn end(self) -> Result<(), ExecError> {
        self.0.end_seq();
        self.0.end_seq();
        Ok(())
    }
}

impl<'a, 'b: 'a> ser::SerializeTupleVariant for SubSerializer<'a, 'b> {
    type Ok = ();
    type Error = ExecError;

    fn serialize_field<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), ExecError> {
        value.serialize(&mut *self.0)
    }

    fn end(self) -> Result<(), ExecError> {
        self.0.end_enum();
        Ok(())
    }
}

impl<'a, 'b: 'a> ser::SerializeMap for SubSerializer<'a, 'b> {
    type Ok = ();
    type Error = ExecError;

    fn serialize_key<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), ExecError> {
        self.0.emit_map_key();
        value.serialize(&mut *self.0)
    }

    fn serialize_value<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), ExecError> {
        value.serialize(&mut *self.0)
    }

    fn end(self) -> Result<(), ExecError> {
        self.0.end_seq();
        Ok(())
    }
}

impl<'a, 'b: 'a> ser::SerializeStruct for SubSerializer<'a, 'b> {
    type Ok = ();
    type Error = ExecError;

    fn serialize_field<T: ?Sized + Serialize>(
        &mut self,
        name: &'static str,
        value: &T,
    ) -> Result<(), ExecError> {
        self.0.field_name(name);
        value.serialize(&mut *self.0)
    }

    fn end(self) -> Result<(), ExecError> {
        self.0.end_struct();
        Ok(())
    }
}

impl<'a, 'b: 'a> ser::SerializeStructVariant for SubSerializer<'a, 'b> {
    type Ok = ();
    type Error = ExecError;

    fn serialize_field<T: ?Sized + Serialize>(
        &mut self,
        name: &'static str,
        value: &T,
    ) -> Result<(), ExecError> {
        self.0.field_name(name);
        value.serialize(&mut *self.0)
    }

    fn end(self) -> Result<(), ExecError> {
        self.0.end_struct();
        Ok(())
    }
}
