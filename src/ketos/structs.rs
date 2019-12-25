//! Implementation of `Struct` and `StructDef` values

use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::fmt;
use std::marker::PhantomData;
use std::rc::Rc;

use crate::error::Error;
use crate::exec::ExecError;
use crate::function::value_is;
use crate::name::{Name, NameMapSlice, NameStore};
use crate::scope::Scope;
use crate::value::{ForeignValue, Value};

/// Implements functionality for Ketos `struct` values on a Rust type.
///
/// A type implementing `StructValue` may be constructed with `new`,
/// will provide field access with `.` and can create modified values with `.=`.
///
/// An implementation of this trait can be generated using `derive(StructValue)`
/// with the `ketos_derive` crate.
pub trait StructValue: Sized + Clone + ForeignValue {
    /// Returns the `struct` name.
    fn struct_name() -> &'static str;

    /// Creates a value from a list of fields.
    ///
    /// An error should be returned if any fields are missing, superfluous,
    /// or the wrong type of value.
    fn from_fields(scope: &Scope, def: &Rc<StructDef>,
        fields: &mut [(Name, Value)]) -> Result<Self, Error>;

    /// Returns a list of field names.
    fn field_names() -> &'static [&'static str];

    /// Returns a copy of a field as a Ketos `Value`.
    ///
    /// If the named field does not exist, an error should be returned.
    fn get_field(&self, scope: &Scope, def: &Rc<StructDef>, name: Name) -> Result<Value, Error>;

    /// Modifies the value to replace named fields with provided values.
    ///
    /// If any names are invalid or any values are of incorrect type,
    /// an error should be returned.
    fn replace_fields(&mut self, scope: &Scope, def: &Rc<StructDef>,
        fields: &mut [(Name, Value)]) -> Result<(), Error>;
}

/// Implements construction and field access for `Struct` and `struct`-like values.
pub trait StructDefinition: Any {
    /// Returns whether the given value is an instance of the given `StructDef`.
    ///
    /// `def` is the `StructDef` instance for this definition.
    fn is_instance(&self, value: &Value, def: &Rc<StructDef>) -> bool;

    /// Creates a value of this `struct` type from the given list of fields.
    ///
    /// `def` is the `StructDef` instance for this definition.
    fn from_fields(&self, scope: &Scope, def: &Rc<StructDef>,
        fields: &mut [(Name, Value)]) -> Result<Value, Error>;

    /// Returns a field from a `struct` value.
    ///
    /// `def` is the `StructDef` instance for this definition.
    fn get_field(&self, scope: &Scope, def: &Rc<StructDef>,
        value: &Value, field: Name) -> Result<Value, Error>;

    /// Returns a list of field names.
    fn field_names(&self) -> Vec<Name>;

    /// Returns a new `struct` value with a set of fields replaced with given values.
    ///
    /// `def` is the `StructDef` instance for this definition.
    fn replace_fields(&self, scope: &Scope, def: &Rc<StructDef>,
        value: Value, fields: &mut [(Name, Value)]) -> Result<Value, Error>;

    /// Returns an estimate of the memory held by this definition.
    ///
    /// The result will be used in applying memory restrictions to executing code.
    /// The result **MUST NOT** change for the lifetime of the value.
    fn size(&self) -> usize { 2 }
}

impl_any_cast!{ StructDefinition }

/// Provides a `StructDefinition` implementation for `StructValue` types.
pub struct ForeignStructDef<T> {
    fields: Vec<Name>,
    data: PhantomData<T>,
}

impl<T: StructValue> ForeignStructDef<T> {
    /// Creates a new `ForeignStructDef`.
    pub fn new(names: &mut NameStore) -> ForeignStructDef<T> {
        ForeignStructDef{
            fields: T::field_names().iter().map(|s| names.add(s)).collect(),
            data: PhantomData,
        }
    }

    fn get<'a>(&self, value: &'a Value) -> &'a T {
        match *value {
            Value::Foreign(ref fv) => {
                // TODO: Panicking here is not ideal.
                fv.downcast_ref::<T>()
                    .expect("invalid foreign value for ForeignStructDef")
            }
            _ => panic!("invalid value for ForeignStructDef")
        }
    }

    fn get_rc(&self, value: Value) -> Rc<T> {
        match value {
            Value::Foreign(fv) => {
                ForeignValue::downcast_rc::<T>(fv)
                    .expect("invalid foreign value for ForeignStructDef")
            }
            _ => panic!("invalid value for ForeignStructDef")
        }
    }
}

impl<T: StructValue> StructDefinition for ForeignStructDef<T> {
    fn is_instance(&self, value: &Value, _def: &Rc<StructDef>) -> bool {
        match *value {
            Value::Foreign(ref fv) => fv.is::<T>(),
            _ => false
        }
    }

    fn from_fields(&self, scope: &Scope, def: &Rc<StructDef>,
            fields: &mut [(Name, Value)]) -> Result<Value, Error> {
        T::from_fields(scope, def, fields).map(Value::new_foreign)
    }

    fn get_field(&self, scope: &Scope, def: &Rc<StructDef>, value: &Value, field: Name) -> Result<Value, Error> {
        let v = self.get(value);
        v.get_field(scope, def, field)
    }

    fn field_names(&self) -> Vec<Name> {
        self.fields.clone()
    }

    fn replace_fields(&self, scope: &Scope, def: &Rc<StructDef>,
            value: Value, fields: &mut [(Name, Value)]) -> Result<Value, Error> {
        let mut v = self.get_rc(value);
        Rc::make_mut(&mut v).replace_fields(scope, def, fields)?;
        Ok(Value::Foreign(v))
    }
}

/// Implements `StructDefinition` for `Struct` values
pub struct StructValueDef {
    fields: NameMapSlice<Name>,
}

impl StructValueDef {
    /// Creates a new `StructValueDef` from a mapping of field name to type name.
    pub fn new(fields: NameMapSlice<Name>) -> StructValueDef {
        StructValueDef{ fields }
    }

    /// Returns a borrowed reference to the contained fields.
    pub fn fields(&self) -> &NameMapSlice<Name> {
        &self.fields
    }

    fn get(&self, name: Name, def: &Rc<StructDef>) -> Result<(usize, Name), ExecError> {
        self.fields.iter().enumerate()
            .find(|&(_, &(n, _))| n == name)
            .map(|(i, &(_, ty))| (i, ty))
            .ok_or_else(|| ExecError::FieldError{
                struct_name: def.name(),
                field: name,
            })
    }
}

impl StructDefinition for StructValueDef {
    fn is_instance(&self, value: &Value, def: &Rc<StructDef>) -> bool {
        match *value {
            Value::Struct(ref s) => s.def() == def,
            _ => false
        }
    }

    fn from_fields(&self, scope: &Scope, def: &Rc<StructDef>, fields: &mut [(Name, Value)]) -> Result<Value, Error> {
        let mut res = vec![Value::Unbound; self.fields.len()];

        for &mut (name, ref mut value) in fields {
            let (idx, ty) = self.get(name, def)?;

            if !value_is(scope, value, ty) {
                return Err(ExecError::FieldTypeError{
                    struct_name: def.name(),
                    field: name,
                    expected: ty,
                    found: value.type_name(),
                    value: Some(value.take()),
                }.into());
            }

            res[idx] = value.take();
        }

        for (i, field) in res.iter().enumerate() {
            if let Value::Unbound = *field {
                let name = self.fields.values()[i].0;

                return Err(ExecError::MissingField{
                    struct_name: def.name(),
                    field: name,
                }.into());
            }
        }

        Ok(Value::Struct(Rc::new(Struct::new(def.clone(), res.into_boxed_slice()))))
    }

    fn get_field(&self, _scope: &Scope, def: &Rc<StructDef>,
            value: &Value, field: Name) -> Result<Value, Error> {
        match *value {
            Value::Struct(ref v) => {
                let (idx, _) = self.get(field, def)?;
                Ok(v.fields[idx].clone())
            }
            ref v => Err(ExecError::expected("struct", v).into())
        }
    }

    fn field_names(&self) -> Vec<Name> {
        self.fields.iter().map(|&(name, _)| name).collect()
    }

    fn replace_fields(&self, scope: &Scope, def: &Rc<StructDef>,
            value: Value, fields: &mut [(Name, Value)]) -> Result<Value, Error> {
        let mut struc = match value {
            Value::Struct(s) => s,
            ref v => return Err(ExecError::expected("struct", v).into())
        };

        {
            let struc_inner = Rc::make_mut(&mut struc);
            let values = struc_inner.fields_mut();

            for &mut (name, ref mut value) in fields {
                let (idx, ty) = self.get(name, def)?;

                if !value_is(scope, value, ty) {
                    return Err(ExecError::FieldTypeError{
                        struct_name: def.name(),
                        field: name,
                        expected: ty,
                        found: value.type_name(),
                        value: Some(value.take()),
                    }.into());
                }

                values[idx] = value.take();
            }
        }

        Ok(Value::Struct(struc))
    }

    fn size(&self) -> usize {
        2 + self.fields.len()
    }
}

/// Represents a structure value containing named fields
#[derive(Clone, Debug)]
pub struct Struct {
    /// Struct definition
    def: Rc<StructDef>,
    /// Struct fields
    fields: Box<[Value]>,
}

impl Struct {
    /// Creates a new `Struct` value with the given `StructDef` and field values.
    pub fn new(def: Rc<StructDef>, fields: Box<[Value]>) -> Struct {
        Struct{ def, fields }
    }

    /// Returns the struct definition.
    pub fn def(&self) -> &Rc<StructDef> {
        &self.def
    }

    /// Returns the field values.
    pub fn fields(&self) -> &[Value] {
        &self.fields
    }

    /// Returns a mutable reference to the field values.
    pub fn fields_mut(&mut self) -> &mut [Value] {
        &mut self.fields
    }
}

/// Represents the definition of a class of struct value
pub struct StructDef {
    /// Struct name
    name: Name,
    /// Implementation of struct definition
    def: Box<dyn StructDefinition>,
}

impl fmt::Debug for StructDef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("StructDef")
            .field("name", &self.name)
            .finish()
    }
}

impl Eq for StructDef {}

impl PartialEq for StructDef {
    fn eq(&self, rhs: &StructDef) -> bool {
        ptr_eq(self, rhs)
    }
}

/// Mapping of `Rc<StructDef>` by `TypeId`.
pub type StructDefMap = HashMap<TypeId, Rc<StructDef>>;

fn ptr_eq<T>(a: *const T, b: *const T) -> bool {
    a == b
}

impl StructDef {
    /// Creates a new `StructDef` with the given name and fields.
    pub fn new(name: Name, def: Box<dyn StructDefinition>) -> StructDef {
        StructDef{ name, def }
    }

    /// Returns the struct name.
    pub fn name(&self) -> Name {
        self.name
    }

    /// Returns a reference to the `StructDefinition` implementation.
    pub fn def(&self) -> &dyn StructDefinition {
        &*self.def
    }
}
