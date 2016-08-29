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

use serde::{Serialize, Serializer};

use exec::{ExecError, panic};
use error::Error;
use name::Name;
use scope::Scope;
use value::Value;

/// Encodes a Rust type into a `Value`.
///
/// See [`value_encode`](index.html) module documentation for details.
pub fn encode_value<T: Serialize>(scope: &Scope, value: &T) -> Result<Value, Error> {
    let mut ser = VSerializer::new(scope);
    try!(value.serialize(&mut ser));
    Ok(ser.value.expect("empty serializer"))
}

impl ::serde::ser::Error for ExecError {
    fn custom<T: Into<String>>(msg: T) -> ExecError {
        panic(msg.into())
    }

    fn invalid_value(msg: &str) -> ExecError {
        panic(format!("invalid value: {}", msg))
    }
}

struct VSerializer<'a> {
    scope: &'a Scope,
    value: Option<Value>,
    state: Vec<SerializeState>,
}

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
        VSerializer{
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
            _ => false
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
                self.state.push(SerializeState::Sequence(Vec::with_capacity(len)));
            }
            _ => panic!("missing begin_enum")
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
                self.state.push(SerializeState::StructKey(
                    Vec::with_capacity(len * 2)));
            }
            _ => panic!("missing begin_enum")
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
        self.state.push(SerializeState::StructKey(Vec::with_capacity(len * 2)));
    }

    fn end_struct(&mut self) {
        match self.state.pop().unwrap() {
            SerializeState::StructKey(v) => {
                self.emit_value(v);
            }
            _ => panic!("missing struct state")
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
        self.state.push(SerializeState::Sequence(Vec::with_capacity(len)));
    }

    // For now, Option values are encoded as:
    //  None    => ()
    //  Some(v) => v
    fn emit_none(&mut self) {
        self.emit_value(());
    }

    fn begin_seq(&mut self, len: usize) {
        self.state.push(SerializeState::Sequence(Vec::with_capacity(len)));
    }

    fn end_seq(&mut self) {
        match self.state.pop().expect("not in sequence") {
            SerializeState::Sequence(v) => {
                self.emit_value(v);
            }
            _ => panic!("missing sequence")
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

impl<'a> Serializer for VSerializer<'a> {
    type Error = ExecError;

    type SeqState = ();
    type TupleState = ();
    type TupleStructState = ();
    type TupleVariantState = ();
    type MapState = ();
    type StructState = ();
    type StructVariantState = ();

    fn serialize_bool(&mut self, v: bool) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_char(&mut self, v: char) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_i8(&mut self, v: i8) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_i16(&mut self, v: i16) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_i32(&mut self, v: i32) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_i64(&mut self, v: i64) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_isize(&mut self, v: isize) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_u8(&mut self, v: u8) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_u16(&mut self, v: u16) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_u32(&mut self, v: u32) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_u64(&mut self, v: u64) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_usize(&mut self, v: usize) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_f32(&mut self, v: f32) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_f64(&mut self, v: f64) -> Result<(), ExecError> {
        self.emit_value(v);
        Ok(())
    }

    fn serialize_str(&mut self, v: &str) -> Result<(), ExecError> {
        self.emit_str(v);
        Ok(())
    }

    fn serialize_bytes(&mut self, v: &[u8]) -> Result<(), ExecError> {
        let mut state = try!(self.serialize_seq(Some(v.len())));

        for b in v {
            try!(self.serialize_seq_elt(&mut state, *b));
        }

        self.serialize_seq_end(state)
    }

    fn serialize_unit(&mut self) -> Result<(), ExecError> {
        self.emit_value(());
        Ok(())
    }

    fn serialize_unit_struct(&mut self, name: &'static str) -> Result<(), ExecError> {
        self.emit_unit_struct(name);
        Ok(())
    }

    fn serialize_unit_variant(&mut self, name: &'static str,
            _index: usize, variant: &'static str) -> Result<(), ExecError> {
        self.emit_unit_variant(name, variant);
        Ok(())
    }

    fn serialize_none(&mut self) -> Result<(), ExecError> {
        self.emit_none();
        Ok(())
    }

    fn serialize_some<V: Serialize>(&mut self, value: V) -> Result<(), ExecError> {
        value.serialize(self)
    }

    fn serialize_seq_fixed_size(&mut self, len: usize) -> Result<(), ExecError> {
        self.serialize_seq(Some(len))
    }

    fn serialize_seq(&mut self, len: Option<usize>) -> Result<(), ExecError> {
        self.begin_seq(len.unwrap_or(0));
        Ok(())
    }

    fn serialize_seq_elt<V: Serialize>(&mut self, _state: &mut (), value: V)
            -> Result<(), ExecError> {
        value.serialize(self)
    }

    fn serialize_seq_end(&mut self, _state: ()) -> Result<(), ExecError> {
        self.end_seq();
        Ok(())
    }

    fn serialize_tuple(&mut self, len: usize) -> Result<(), ExecError> {
        self.serialize_seq(Some(len))
    }

    fn serialize_tuple_elt<T>(&mut self, state: &mut (), value: T)
            -> Result<(), ExecError> where T: Serialize {
        self.serialize_seq_elt(state, value)
    }

    fn serialize_tuple_end(&mut self, state: ()) -> Result<(), ExecError> {
        self.serialize_seq_end(state)
    }

    fn serialize_map(&mut self, len: Option<usize>) -> Result<(), ExecError> {
        self.begin_seq(len.unwrap_or(0));
        Ok(())
    }

    fn serialize_map_key<T>(&mut self, _state: &mut (), key: T)
            -> Result<(), ExecError> where T: Serialize {
        self.emit_map_key();
        key.serialize(self)
    }

    fn serialize_map_value<T>(&mut self, _state: &mut (), value: T)
            -> Result<(), ExecError> where T: Serialize {
        value.serialize(self)
    }

    fn serialize_map_end(&mut self, _state: ()) -> Result<(), ExecError> {
        self.end_seq();
        Ok(())
    }

    fn serialize_struct(&mut self, name: &'static str, len: usize)
            -> Result<(), ExecError> {
        self.begin_struct(name, len);
        Ok(())
    }

    fn serialize_struct_elt<T>(&mut self, _state: &mut (),
            name: &'static str, value: T)
            -> Result<(), ExecError> where T: Serialize {
        self.field_name(name);
        value.serialize(self)
    }

    fn serialize_struct_end(&mut self, _state: ()) -> Result<(), ExecError> {
        self.end_struct();
        Ok(())
    }

    fn serialize_newtype_struct<T>(&mut self, name: &'static str, value: T)
            -> Result<(), ExecError> where T: Serialize {
        let mut state = try!(self.serialize_tuple_struct(name, 1));

        try!(self.serialize_tuple_struct_elt(&mut state, value));

        self.serialize_tuple_struct_end(state)
    }

    fn serialize_tuple_struct(&mut self, name: &'static str, len: usize)
            -> Result<(), ExecError> {
        self.begin_tuple_struct(name, len);
        Ok(())
    }

    fn serialize_tuple_struct_elt<T>(&mut self, _state: &mut (), value: T)
            -> Result<(), ExecError> where T: Serialize {
        value.serialize(self)
    }

    fn serialize_tuple_struct_end(&mut self, _state: ()) -> Result<(), ExecError> {
        self.end_seq();
        self.end_seq();
        Ok(())
    }

    fn serialize_newtype_variant<T>(&mut self, name: &'static str,
            index: usize, variant: &'static str, value: T)
            -> Result<(), ExecError> where T: Serialize {
        let mut state = try!(self.serialize_tuple_variant(name, index, variant, 1));

        try!(self.serialize_tuple_variant_elt(&mut state, value));

        self.serialize_tuple_variant_end(state)
    }

    fn serialize_tuple_variant(&mut self, name: &'static str,
            _index: usize, variant: &'static str, len: usize)
            -> Result<(), ExecError> {
        self.begin_enum(name);
        self.enum_variant(variant, len);
        Ok(())
    }

    fn serialize_tuple_variant_elt<T>(&mut self, _state: &mut (), value: T)
            -> Result<(), ExecError> where T: Serialize {
        value.serialize(self)
    }

    fn serialize_tuple_variant_end(&mut self, _state: ()) -> Result<(), ExecError> {
        self.end_enum();
        Ok(())
    }

    fn serialize_struct_variant(&mut self, name: &'static str,
            _index: usize, variant: &'static str, len: usize)
            -> Result<(), ExecError> {
        self.begin_enum(name);
        self.struct_variant(variant, len);
        Ok(())
    }

    fn serialize_struct_variant_elt<T>(&mut self, _state: &mut (),
            key: &'static str, value: T)
            -> Result<(), ExecError> where T: Serialize {
        self.field_name(key);
        value.serialize(self)
    }

    fn serialize_struct_variant_end(&mut self, _state: ()) -> Result<(), ExecError> {
        self.end_struct();
        Ok(())
    }
}
