//! Represents any possible value type.

use std::any::{Any, TypeId};
use std::cmp::Ordering;
use std::fmt;
use std::mem::{replace, transmute};
use std::rc::Rc;

use error::Error;
use exec::{Context, ExecError};
use function::{Function, Lambda};
use integer::{Integer, Ratio};
use name::{Name, NameDebug, NameDisplay, NameMapSlice, NameStore};
use rc_vec::RcVec;

/// Represents a value.
#[derive(Clone, Debug)]
pub enum Value {
    /// `()`
    Unit,
    /// Placeholder for missing optional values;
    /// should not be used to represent any real value.
    Unbound,
    /// Boolean -- `true` or `false`
    Bool(bool),
    /// Floating point number
    Float(f64),
    /// Signed arbitrary precision integer
    Integer(Integer),
    /// Arbitrary precision ratio
    Ratio(Ratio),
    /// Struct value
    Struct(Rc<Struct>),
    /// Struct definition
    StructDef(Rc<StructDef>),
    /// Literal name
    Name(Name),
    /// Keyword
    Keyword(Name),
    /// Character
    Char(char),
    /// String
    String(String),
    /// Quasiquoted value; quote depth **MUST NEVER be zero.**
    Quasiquote(Box<Value>, u32),
    /// Comma'd value; comma depth **MUST NEVER be zero.**
    Comma(Box<Value>, u32),
    /// Comma-at'd value; quote depth **MUST NEVER be zero**.
    CommaAt(Box<Value>, u32),
    /// Quoted value; quote depth **MUST NEVER be zero**.
    Quote(Box<Value>, u32),
    /// Series of one or more values.
    /// **MUST NEVER be of length zero.** Use `Unit` to represent empty lists.
    List(RcVec<Value>),
    /// Function implemented in Rust
    Function(Function),
    /// Compiled bytecode function
    Lambda(Lambda),
    /// Boxed value of a foreign type
    Foreign(Rc<ForeignValue>),
}

impl Value {
    /// Returns a value of a foreign type.
    pub fn new_foreign<T: ForeignValue>(t: T) -> Value {
        Value::Foreign(Rc::new(t))
    }

    /// Returns a value containing a foreign function.
    pub fn new_foreign_fn<F>(name: Name, f: F) -> Value
            where F: Any + Fn(&Context, &mut [Value]) -> Result<Value, Error> {
        Value::new_foreign(ForeignFn{
            name: name,
            f: f,
        })
    }

    /// Compares two values; returns an error if the values cannot be compared.
    pub fn compare(&self, rhs: &Value) -> Result<Ordering, ExecError> {
        let ord = match (self, rhs) {
            (&Value::Unit, &Value::Unit) => Ordering::Equal,
            (&Value::Bool(a), &Value::Bool(b)) => a.cmp(&b),
            (&Value::Float(a), &Value::Float(b)) =>
                try!(a.partial_cmp(&b).ok_or(ExecError::CompareNaN)),
            (&Value::Integer(ref a), &Value::Integer(ref b)) => a.cmp(&b),
            (&Value::Ratio(ref a), &Value::Ratio(ref b)) => a.cmp(&b),
            (&Value::Name(a), &Value::Name(b)) => a.cmp(&b),
            (&Value::Keyword(a), &Value::Keyword(b)) => a.cmp(&b),
            (&Value::Char(a), &Value::Char(b)) => a.cmp(&b),
            (&Value::String(ref a), &Value::String(ref b)) => a.cmp(&b),
            (&Value::Unit, &Value::List(_)) => Ordering::Less,
            (&Value::List(_), &Value::Unit) => Ordering::Greater,
            (&Value::List(ref a), &Value::List(ref b)) =>
                try!(cmp_value_slice(a, b)),
            (&Value::Struct(ref a), &Value::Struct(ref b)) => {
                if a.def == b.def {
                    try!(cmp_value_iter(
                        a.fields.iter().map(|&(_, ref v)| v).zip(
                            b.fields.iter().map(|&(_, ref v)| v))))
                } else {
                    return Err(ExecError::StructMismatch{
                        lhs: a.def.name,
                        rhs: b.def.name,
                    });
                }
            }

            // Coercible numeric comparisons
            (&Value::Float(ref a), &Value::Integer(ref b)) => {
                let b = try!(b.to_f64().ok_or(ExecError::Overflow));
                try!(a.partial_cmp(&b).ok_or(ExecError::CompareNaN))
            }
            (&Value::Float(ref a), &Value::Ratio(ref b)) => {
                let b = try!(b.to_f64().ok_or(ExecError::Overflow));
                try!(a.partial_cmp(&b).ok_or(ExecError::CompareNaN))
            }
            (&Value::Integer(ref a), &Value::Float(ref b)) => {
                let a = try!(a.to_f64().ok_or(ExecError::Overflow));
                try!(a.partial_cmp(b).ok_or(ExecError::CompareNaN))
            }
            (&Value::Integer(ref a), &Value::Ratio(ref b)) => {
                let a = Ratio::from_integer(a.clone());
                a.cmp(b)
            }
            (&Value::Ratio(ref a), &Value::Float(ref b)) => {
                let a = try!(a.to_f64().ok_or(ExecError::Overflow));
                try!(a.partial_cmp(b).ok_or(ExecError::CompareNaN))
            }
            (&Value::Ratio(ref a), &Value::Integer(ref b)) => {
                let b = Ratio::from_integer(b.clone());
                a.cmp(&b)
            }

            // Non-comparable types
            (&Value::StructDef(_), &Value::StructDef(_)) =>
                return Err(ExecError::CannotCompare("struct-def")),
            (&Value::Function(_), &Value::Function(_)) =>
                return Err(ExecError::CannotCompare("function")),
            (&Value::Lambda(_), &Value::Lambda(_)) =>
                return Err(ExecError::CannotCompare("lambda")),
            (&Value::Quote(_, _), &Value::Quote(_, _)) =>
                return Err(ExecError::CannotCompare("quote")),
            (&Value::Quasiquote(_, _), &Value::Quasiquote(_, _)) =>
                return Err(ExecError::CannotCompare("quasiquote")),
            (&Value::Comma(_, _), &Value::Comma(_, _)) =>
                return Err(ExecError::CannotCompare("comma")),
            (&Value::CommaAt(_, _), &Value::CommaAt(_, _)) =>
                return Err(ExecError::CannotCompare("comma-at")),

            (&Value::Foreign(ref a), ref b) => try!(a.compare_to_value(b)),
            (ref a, &Value::Foreign(ref b)) =>
                flip_ordering(try!(b.compare_to_value(a))),

            // Type mismatch
            (a, b) => return Err(ExecError::TypeMismatch{
                lhs: a.type_name(),
                rhs: b.type_name(),
            })
        };

        Ok(ord)
    }

    /// Tests two values for equality; returns an error if the values cannot be
    /// compared.
    pub fn is_equal(&self, rhs: &Value) -> Result<bool, ExecError> {
        let eq = match (self, rhs) {
            (&Value::Unit, &Value::Unit) => true,
            (&Value::Bool(a), &Value::Bool(b)) => a == b,
            (&Value::Float(a), &Value::Float(b)) => a == b,
            (&Value::Integer(ref a), &Value::Integer(ref b)) => a == b,
            (&Value::Ratio(ref a), &Value::Ratio(ref b)) => a == b,

            (&Value::Float(a), &Value::Integer(ref b)) => {
                let b = try!(b.to_f64().ok_or(ExecError::Overflow));
                a == b
            }
            (&Value::Float(a), &Value::Ratio(ref b)) => {
                let b = try!(b.to_f64().ok_or(ExecError::Overflow));
                a == b
            }
            (&Value::Integer(ref a), &Value::Float(b)) => {
                let a = try!(a.to_f64().ok_or(ExecError::Overflow));
                a == b
            }
            (&Value::Ratio(ref a), &Value::Float(b)) => {
                let a = try!(a.to_f64().ok_or(ExecError::Overflow));
                a == b
            }

            (&Value::Integer(ref a), &Value::Ratio(ref b)) => a == b,
            (&Value::Ratio(ref a), &Value::Integer(ref b)) => a == b,

            (&Value::Name(a), &Value::Name(b)) => a == b,
            (&Value::Keyword(a), &Value::Keyword(b)) => a == b,
            (&Value::Char(a), &Value::Char(b)) => a == b,
            (&Value::String(ref a), &Value::String(ref b)) => a == b,
            (&Value::Quote(ref a, na), &Value::Quote(ref b, nb)) =>
                na == nb && try!(a.is_equal(&b)),
            (&Value::Unit, &Value::List(_)) => false,
            (&Value::List(_), &Value::Unit) => false,
            (&Value::List(ref a), &Value::List(ref b)) =>
                try!(eq_value_slice(a, b)),
            (&Value::Struct(ref a), &Value::Struct(ref b)) => {
                if a.def == b.def {
                    try!(eq_value_iter(a.fields.iter().zip(b.fields.iter())
                        .map(|(&(_, ref a), &(_, ref b))| (a, b))))
                } else {
                    return Err(ExecError::StructMismatch{
                        lhs: a.def.name,
                        rhs: b.def.name,
                    });
                }
            }
            (&Value::StructDef(ref a), &Value::StructDef(ref b)) => a == b,
            (&Value::Function(ref a), &Value::Function(ref b)) => a == b,
            (&Value::Lambda(ref a), &Value::Lambda(ref b)) => a == b,

            (&Value::Foreign(ref a), ref b) => try!(a.is_equal_to_value(b)),
            (ref a, &Value::Foreign(ref b)) => try!(b.is_equal_to_value(a)),

            (a, b) => return Err(ExecError::TypeMismatch{
                lhs: a.type_name(),
                rhs: b.type_name(),
            })
        };

        Ok(eq)
    }

    /// Returns whether this value is identical to another.
    /// The notable difference between this and `eq` is that float `NaN` values
    /// will compare equal.
    pub fn is_identical(&self, rhs: &Value) -> bool {
        match (self, rhs) {
            (&Value::Unit, &Value::Unit) => true,
            (&Value::Unbound, &Value::Unbound) => true,
            (&Value::Bool(a), &Value::Bool(b)) => a == b,
            (&Value::Float(a), &Value::Float(b)) => float_is_identical(a, b),
            (&Value::Integer(ref a), &Value::Integer(ref b)) => a == b,
            (&Value::Ratio(ref a), &Value::Ratio(ref b)) => a == b,
            (&Value::Struct(ref a), &Value::Struct(ref b)) =>
                a.def == b.def &&
                    a.fields.iter().zip(b.fields.iter())
                        .all(|(&(_, ref a), &(_, ref b))| a.is_identical(b)),
            (&Value::Name(a), &Value::Name(b)) => a == b,
            (&Value::Keyword(a), &Value::Keyword(b)) => a == b,
            (&Value::Char(a), &Value::Char(b)) => a == b,
            (&Value::String(ref a), &Value::String(ref b)) => a == b,
            (&Value::Quasiquote(ref a, na), &Value::Quasiquote(ref b, nb)) =>
                na == nb && a.is_identical(b),
            (&Value::Comma(ref a, na), &Value::Comma(ref b, nb)) =>
                na == nb && a.is_identical(b),
            (&Value::Quote(ref a, na), &Value::Quote(ref b, nb)) =>
                na == nb && a.is_identical(b),
            (&Value::List(ref a), &Value::List(ref b)) =>
                list_is_identical(a, b),
            (&Value::Function(ref a), &Value::Function(ref b)) => a == b,
            (&Value::Lambda(ref a), &Value::Lambda(ref b)) => a == b,

            (&Value::Foreign(ref a), &Value::Foreign(ref b)) =>
                a.is_identical_to(&**b),

            _ => false
        }
    }

    /// Replaces the value with `Unit` and returns the old value.
    pub fn take(&mut self) -> Value {
        replace(self, Value::Unit)
    }

    /// Returns the value, quasi-quoted.
    pub fn quasiquote(self, n: u32) -> Value {
        match self {
            Value::Quasiquote(v, i) => Value::Quasiquote(v, i + n),
            v => Value::Quasiquote(Box::new(v), n),
        }
    }

    #[doc(hidden)]
    // Estimates the size of memory held by the value.
    // Used in applying restrictions to code execution.
    pub fn size(&self) -> usize {
        match *self {
            Value::Integer(ref i) => 1 + i.bits() / 8,
            Value::Ratio(ref r) => {
                let numer = r.numer().bits();
                let denom = r.denom().bits();
                1 + numer + denom
            }
            Value::Struct(ref s) =>
                1 + s.fields.iter().map(|&(_, ref f)| f.size()).fold(0, |a, b| a + b),
            Value::StructDef(ref d) => 1 + d.fields.len(),
            Value::String(ref s) => 1 + s.len(),
            Value::Comma(ref v, _) |
            Value::CommaAt(ref v, _) |
            Value::Quasiquote(ref v, _) |
            Value::Quote(ref v, _) => 1 + v.size(),
            Value::List(ref li) =>
                1 + li.iter().map(|v| v.size()).fold(0, |a, b| a + b),
            Value::Lambda(ref l) =>
                1 + l.values.as_ref().map_or(0,
                    |v| v.iter().map(|v| v.size()).fold(0, |a, b| a + b)),
            Value::Foreign(ref v) => v.size(),
            _ => 1
        }
    }

    /// Returns the value, comma'd.
    pub fn comma(self, n: u32) -> Value {
        match self {
            Value::Comma(v, i) => Value::Comma(v, i + n),
            Value::CommaAt(v, i) => Value::CommaAt(v, i + n),
            v => Value::Comma(Box::new(v), n),
        }
    }

    /// Returns the value, comma-at'd.
    pub fn comma_at(self, n: u32) -> Value {
        match self {
            Value::CommaAt(v, i) => Value::CommaAt(v, i + n),
            v => Value::CommaAt(Box::new(v), n)
        }
    }

    /// Returns the value, quoted.
    pub fn quote(self, n: u32) -> Value {
        match self {
            Value::Quote(v, i) => Value::Quote(v, i + n),
            v => Value::Quote(Box::new(v), n),
        }
    }

    /// Returns a string describing the type of the value.
    pub fn type_name(&self) -> &'static str {
        match *self {
            Value::Unit => "unit",
            Value::Unbound => "<unbound>",
            Value::Bool(_) => "bool",
            Value::Float(_) => "float",
            Value::Integer(_) => "integer",
            Value::Ratio(_) => "ratio",
            Value::Char(_) => "char",
            Value::String(_) => "string",
            Value::Name(_) => "name",
            Value::Keyword(_) => "keyword",
            // XXX: Does this make sense?
            Value::Quasiquote(_, _) |
            Value::Comma(_, _) |
            Value::CommaAt(_, _) |
            Value::Quote(_, _) => "object",
            Value::List(_) => "list",
            Value::Struct(_) => "struct",
            Value::StructDef(_) => "struct-def",
            Value::Function(_) => "function",
            Value::Lambda(_) => "lambda",
            Value::Foreign(ref a) => a.type_name(),
        }
    }
}

/// A helper trait that is necessary as long as `Any::get_type_id` is unstable.
pub trait AnyValue: Any {
    /// Returns the `TypeId` value for the type.
    fn type_id(&self) -> TypeId;
}

impl<T: Any> AnyValue for T {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }
}

/// Duplicate definition of `std::raw::TraitObject`, which is unstable.
#[repr(C)]
struct TraitObject {
    pub data: *mut (),
    pub vtable: *mut (),
}

/// Represents a type of value defined outside the core interpreter.
pub trait ForeignValue: AnyValue + fmt::Debug {
    /// Performs ordered comparison between two values of a foreign type.
    ///
    /// If a true, `Ord`-like comparison cannot be made,
    /// `ExecError::CannotCompare(..)` should be returned.
    ///
    /// The default implementation unconditionally returns an error.
    fn compare_to(&self, _rhs: &ForeignValue) -> Result<Ordering, ExecError> {
        Err(ExecError::CannotCompare(self.type_name()))
    }

    /// Performs ordered comparison between two values.
    ///
    /// This method need only be implemented if a value of the foreign type
    /// may be compared with core value types.
    fn compare_to_value(&self, rhs: &Value) -> Result<Ordering, ExecError> {
        match *rhs {
            Value::Foreign(ref rhs) => self.compare_to(&**rhs),
            ref v => Err(ExecError::expected(self.type_name(), v))
        }
    }

    /// Returns whether the two values are identical.
    /// This concept is the same as equality, except in the case of floating
    /// point values, where two `NaN` values are considered identical.
    ///
    /// A type implementing `ForeignValue` need only implement `is_identical`
    /// if it contains a float-type value or emulates some equality relationship
    /// similar to `NaN`.
    fn is_identical_to(&self, rhs: &ForeignValue) -> bool {
        self.is_equal_to(rhs).unwrap_or(false)
    }

    /// Tests for equality between two values of a foreign type.
    ///
    /// The default implementation unconditionally returns an error.
    fn is_equal_to(&self, rhs: &ForeignValue) -> Result<bool, ExecError> {
        Err(ExecError::TypeMismatch{
            lhs: self.type_name(),
            rhs: rhs.type_name(),
        })
    }

    /// Tests for equality between two values.
    ///
    /// This method need only be implemented if a value of the foreign type
    /// may be compared with core value types.
    fn is_equal_to_value(&self, rhs: &Value) -> Result<bool, ExecError> {
        match *rhs {
            Value::Foreign(ref rhs) => self.is_equal_to(&**rhs),
            ref v => Err(ExecError::expected(self.type_name(), v))
        }
    }

    /// Format the value in debugging mode.
    ///
    /// The default implementation uses the type's `fmt::Debug` representation.
    fn fmt_debug(&self, _names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }

    /// Format the value in display mode.
    ///
    /// The default implementation formats the value in debugging mode.
    fn fmt_display(&self, names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_debug(names, f)
    }

    /// Return the value's type name.
    fn type_name(&self) -> &'static str;

    /// Returns whether this value is of the named type.
    ///
    /// The default implementation checks against the value of `self.type_name()`.
    fn is_type(&self, name: &str) -> bool {
        self.type_name() == name
    }

    /// Calls the value as a function.
    ///
    /// The default implementation unconditionally returns an error.
    fn call_value(&self, _ctx: &Context, _args: &mut [Value])
            -> Result<Value, Error> {
        Err(From::from(ExecError::TypeError{
            expected: "function",
            found: self.type_name(),
            value: None,
        }))
    }

    /// Returns an estimate of the memory held by this value.
    ///
    /// The result will be used in applying memory restrictions to executing code.
    /// The result **MUST NOT** change for the lifetime of the value.
    fn size(&self) -> usize { 2 }
}

impl ForeignValue {
    /// Returns whether the contained value is of the given type.
    pub fn is<T: Any>(&self) -> bool {
        self.type_id() == TypeId::of::<T>()
    }

    /// Returns a reference to the contained value, if it is of the given type.
    pub fn downcast_ref<T: Any>(&self) -> Option<&T> {
        if self.is::<T>() {
            unsafe {
                let obj: TraitObject = transmute(self);
                Some(&*(obj.data as *const T))
            }
        } else {
            None
        }
    }

    /// Returns a mutable reference to the contained value,
    /// if it is of the given type.
    pub fn downcast_mut<T: Any>(&mut self) -> Option<&mut T> {
        if self.is::<T>() {
            unsafe {
                let obj: TraitObject = transmute(self);
                Some(&mut *(obj.data as *mut T))
            }
        } else {
            None
        }
    }
}

/// Represents a foreign value that contains a callable function or closure
pub struct ForeignFn<F> {
    name: Name,
    f: F,
}

impl<F> fmt::Debug for ForeignFn<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("ForeignFn { ... }")
    }
}

impl<F> ForeignValue for ForeignFn<F>
        where F: Any + Fn(&Context, &mut [Value]) -> Result<Value, Error> {
    fn compare_to(&self, _rhs: &ForeignValue) -> Result<Ordering, ExecError> {
        Err(ExecError::CannotCompare("foreign-fn"))
    }

    fn fmt_debug(&self, names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<foreign-fn {}>", names.get(self.name))
    }

    fn type_name(&self) -> &'static str { "foreign-fn" }

    fn call_value(&self, ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
        (self.f)(ctx, args)
    }
}

/// Creates a foreign function that implicitly converts input arguments
/// into Rust values and converts its result into a `ketos` value.
///
/// This function is added to the given scope with the given name.
///
/// ```ignore
/// fn foo(a: &str) -> Result<String, Error> { ... }
///
/// ketos_fn!{ scope => "my-fn" => fn foo(a: &str) -> String }
/// ```
#[macro_export]
macro_rules! ketos_fn {
    ( $scope:expr => $name:expr => fn $ident:ident
            ( $( $arg:ident : $arg_ty:ty ),* ) -> $res:ty ) => {
        $scope.add_value_with_name($name,
            |name| $crate::value::Value::new_foreign_fn(name, move |_scope, args| {
                let mut iter = (&*args).iter();

                let _expected = 0 $( + { stringify!($arg); 1 } )*;
                let mut _found = 0;

                let res = try!($ident(
                    $( {
                        match iter.next() {
                            Some(v) => {
                                _found += 1;
                                try!(<$arg_ty as $crate::value::FromValueRef>::from_value_ref(v))
                            }
                            None => return Err(From::from($crate::exec::ExecError::ArityError{
                                name: Some(name),
                                expected: $crate::function::Arity::Exact(_expected),
                                found: _found,
                            }))
                        }
                    } ),*
                ));

                Ok(<$res as Into<$crate::value::Value>>::into(res))
            }))
    }
}

impl NameDebug for Value {
    fn fmt(&self, names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Value::Unit => write!(f, "()"),
            Value::Unbound => write!(f, "<unbound>"),
            Value::Bool(b) => write!(f, "{:?}", b),
            Value::Float(fl) => if is_normal(fl) && fl.trunc() == fl {
                write!(f, "{:?}.0", fl)
            } else {
                write!(f, "{}", fl)
            },
            Value::Integer(ref i) => write!(f, "{}", i),
            Value::Ratio(ref r) => if r.is_integer() {
                write!(f, "{}/1", r)
            } else {
                write!(f, "{}", r)
            },
            Value::Char(ch) => write!(f, "#{:?}", ch),
            Value::String(ref s) => write!(f, "{:?}", s),
            Value::Name(name) => write!(f, "{}", names.get(name)),
            Value::Keyword(name) => write!(f, ":{}", names.get(name)),
            Value::Quasiquote(ref v, depth) => {
                for _ in 0..depth { try!(write!(f, "`")); }
                NameDebug::fmt(v, names, f)
            }
            Value::Comma(ref v, depth) => {
                for _ in 0..depth { try!(write!(f, ",")); }
                NameDebug::fmt(v, names, f)
            }
            Value::CommaAt(ref v, depth) => {
                for _ in 0..depth { try!(write!(f, ",")); }
                try!(write!(f, "@"));
                NameDebug::fmt(v, names, f)
            }
            Value::Quote(ref v, depth) => {
                for _ in 0..depth { try!(write!(f, "'")); }
                NameDebug::fmt(v, names, f)
            }
            Value::List(ref l) => {
                try!(write!(f, "("));

                let mut iter = l.iter();

                if let Some(v) = iter.next() {
                    try!(NameDebug::fmt(v, names, f));
                }

                for v in iter {
                    try!(write!(f, " "));
                    try!(NameDebug::fmt(v, names, f));
                }

                write!(f, ")")
            }
            // TODO: This output doesn't match the way structs are built.
            // Write out "(new 'name ...)"? Implement a shortcut syntax?
            Value::Struct(ref s) => {
                if s.fields.is_empty() {
                    write!(f, "{} {{}}", names.get(s.def.name))
                } else {
                    try!(write!(f, "{} {{ ", names.get(s.def.name)));

                    let mut iter = s.fields.iter();

                    if let Some(&(name, ref value)) = iter.next() {
                        try!(write!(f, "{}: ", names.get(name)));
                        try!(NameDebug::fmt(value, names, f));
                    }

                    for &(name, ref value) in iter {
                        try!(write!(f, ", {}: ", names.get(name)));
                        try!(NameDebug::fmt(value, names, f));
                    }

                    write!(f, " }}")
                }
            }
            Value::StructDef(ref d) => {
                if d.fields.is_empty() {
                    write!(f, "{} def {{}}", names.get(d.name))
                } else {
                    try!(write!(f, "{} def {{ ", names.get(d.name)));

                    let mut iter = d.fields.iter();

                    if let Some(&(name, ty)) = iter.next() {
                        try!(write!(f, "{}: {}", names.get(name), names.get(ty)));
                    }

                    for &(name, ty) in iter {
                        try!(write!(f, ", {}: {}", names.get(name), names.get(ty)));
                    }

                    write!(f, " }}")
                }
            }
            Value::Function(ref fun) =>
                write!(f, "<function {}>", names.get(fun.name)),
            Value::Lambda(ref c) => match c.code.name {
                Some(name) => write!(f, "<lambda {}>", names.get(name)),
                None => write!(f, "<lambda>"),
            },
            Value::Foreign(ref v) => v.fmt_debug(names, f),
        }
    }
}

impl NameDisplay for Value {
    fn fmt(&self, names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Value::Float(fl) => if is_normal(fl) && fl.trunc() == fl {
                write!(f, "{}.0", fl)
            } else {
                write!(f, "{}", fl)
            },
            Value::Char(ch) => write!(f, "{}", ch),
            Value::String(ref s) => write!(f, "{}", s),
            Value::Foreign(ref v) => v.fmt_display(names, f),
            ref v => NameDebug::fmt(v, names, f),
        }
    }
}

fn is_normal(f: f64) -> bool {
    !f.is_nan() && f.is_finite()
}

fn flip_ordering(ord: Ordering) -> Ordering {
    match ord {
        Ordering::Equal => Ordering::Equal,
        Ordering::Greater => Ordering::Less,
        Ordering::Less => Ordering::Greater,
    }
}

fn cmp_value_iter<'a, I>(iter: I) -> Result<Ordering, ExecError>
        where I: IntoIterator<Item=(&'a Value, &'a Value)> {
    for (a, b) in iter {
        match try!(a.compare(b)) {
            Ordering::Equal => (),
            ord => return Ok(ord),
        }
    }

    Ok(Ordering::Equal)
}

fn cmp_value_slice(a: &[Value], b: &[Value]) -> Result<Ordering, ExecError> {
    for (a, b) in a.iter().zip(b) {
        match try!(a.compare(b)) {
            Ordering::Equal => (),
            ord => return Ok(ord),
        }
    }

    Ok(a.len().cmp(&b.len()))
}

fn eq_value_iter<'a, I>(iter: I) -> Result<bool, ExecError>
        where I: IntoIterator<Item=(&'a Value, &'a Value)> {
    for (a, b) in iter {
        if !try!(a.is_equal(b)) {
            return Ok(false);
        }
    }

    Ok(true)
}

fn eq_value_slice(a: &[Value], b: &[Value]) -> Result<bool, ExecError> {
    if a.len() != b.len() {
        return Ok(false);
    }

    for (a, b) in a.iter().zip(b.iter()) {
        if !try!(a.is_equal(b)) {
            return Ok(false);
        }
    }

    Ok(true)
}

fn float_is_identical(a: f64, b: f64) -> bool {
    if a.is_nan() {
        b.is_nan()
    } else {
        a == b
    }
}

fn list_is_identical(a: &[Value], b: &[Value]) -> bool {
    a.len() == b.len() &&
        a.iter().zip(b.iter()).all(|(a, b)| a.is_identical(b))
}

/// Borrows a Rust value from a `Value`
pub trait FromValueRef<'a>: Sized {
    /// Returns the borrowed value
    fn from_value_ref(v: &'a Value) -> Result<Self, ExecError>;
}

macro_rules! simple_from_ref {
    ( $ty:ty ; $pat:pat => $expr:expr ; $ty_name:expr ) => {
        impl<'a> FromValueRef<'a> for $ty {
            fn from_value_ref(v: &'a Value) -> Result<$ty, ExecError> {
                match *v {
                    $pat => Ok($expr),
                    ref v => Err(ExecError::expected($ty_name, v))
                }
            }
        }
    }
}

macro_rules! integer_from_ref {
    ( $ty:ident $meth:ident ) => {
        impl<'a> FromValueRef<'a> for $ty {
            fn from_value_ref(v: &'a Value) -> Result<$ty, ExecError> {
                match *v {
                    Value::Integer(ref i) => i.$meth().ok_or(ExecError::Overflow),
                    ref v => Err(ExecError::expected("integer", v))
                }
            }
        }
    }
}

/// Generates conversion trait implementations for the given type.
///
/// ```ignore
/// foreign_type_conversions!{ MyType => "my-type" }
/// ```
#[macro_export]
macro_rules! foreign_type_conversions {
    ( $ty:ty => $name:expr ) => {
        impl<'a> $crate::value::FromValueRef<'a> for &'a $ty {
            fn from_value_ref(v: &'a $crate::value::Value)
                    -> Result<&'a $ty, $crate::exec::ExecError> {
                match *v {
                    $crate::value::Value::Foreign(ref v) => {
                        if let Some(v) = v.downcast_ref::<$ty>() {
                            return Ok(v);
                        }
                    }
                    _ => ()
                }

                Err($crate::exec::ExecError::expected($name, v))
            }
        }

        impl From<$ty> for $crate::value::Value {
            fn from(v: $ty) -> $crate::value::Value {
                $crate::value::Value::new_foreign(v)
            }
        }
    }
}

simple_from_ref!{ (); Value::Unit => (); "unit" }
simple_from_ref!{ bool; Value::Bool(b) => b; "bool" }
simple_from_ref!{ char; Value::Char(ch) => ch; "char" }
simple_from_ref!{ f32; Value::Float(f) => f as f32; "float" }
simple_from_ref!{ f64; Value::Float(f) => f; "float" }

integer_from_ref!{ i8 to_i8 }
integer_from_ref!{ i16 to_i16 }
integer_from_ref!{ i32 to_i32 }
integer_from_ref!{ i64 to_i64 }
integer_from_ref!{ isize to_isize }
integer_from_ref!{ u8 to_u8 }
integer_from_ref!{ u16 to_u16 }
integer_from_ref!{ u32 to_u32 }
integer_from_ref!{ u64 to_u64 }
integer_from_ref!{ usize to_usize }

impl<'a> FromValueRef<'a> for &'a str {
    fn from_value_ref(v: &'a Value) -> Result<&'a str, ExecError> {
        match *v {
            Value::String(ref s) => Ok(s),
            ref v => Err(ExecError::expected("string", v))
        }
    }
}

impl<'a> FromValueRef<'a> for &'a Integer {
    fn from_value_ref(v: &'a Value) -> Result<&'a Integer, ExecError> {
        match *v {
            Value::Integer(ref i) => Ok(i),
            ref v => Err(ExecError::expected("integer", v))
        }
    }
}

impl<'a> FromValueRef<'a> for &'a Ratio {
    fn from_value_ref(v: &'a Value) -> Result<&'a Ratio, ExecError> {
        match *v {
            Value::Ratio(ref r) => Ok(r),
            ref v => Err(ExecError::expected("ratio", v))
        }
    }
}

impl<'a> FromValueRef<'a> for &'a [Value] {
    fn from_value_ref(v: &'a Value) -> Result<&'a [Value], ExecError> {
        match *v {
            Value::Unit => Ok(&[]),
            Value::List(ref li) => Ok(li),
            ref v => Err(ExecError::expected("list", v))
        }
    }
}

impl<'a, T: FromValueRef<'a>> FromValueRef<'a> for Vec<T> {
    fn from_value_ref(v: &'a Value) -> Result<Vec<T>, ExecError> {
        match *v {
            Value::Unit => Ok(Vec::new()),
            Value::List(ref li) => li.iter()
                .map(|v| T::from_value_ref(v)).collect(),
            ref v => Err(ExecError::expected("list", v))
        }
    }
}

impl<'a> FromValueRef<'a> for &'a Lambda {
    fn from_value_ref(v: &'a Value) -> Result<&'a Lambda, ExecError> {
        match *v {
            Value::Lambda(ref l) => Ok(l),
            ref v => Err(ExecError::expected("lambda", v))
        }
    }
}

impl<'a> FromValueRef<'a> for &'a Value {
    #[inline]
    fn from_value_ref(v: &'a Value) -> Result<&'a Value, ExecError> {
        Ok(v)
    }
}

/// Consumes a `Value` and returns a Rust value
pub trait FromValue: Sized {
    /// Consumes the `Value` and returns a Rust value
    fn from_value(v: Value) -> Result<Self, ExecError>;
}

macro_rules! simple_from_value {
    ( $ty:ty ; $ty_name:expr ; $pat:pat => $expr:expr ) => {
        impl FromValue for $ty {
            fn from_value(v: Value) -> Result<$ty, ExecError> {
                match v {
                    $pat => Ok($expr),
                    ref v => Err(ExecError::expected($ty_name, v))
                }
            }
        }
    }
}

macro_rules! integer_from_value {
    ( $ty:ident $meth:ident ) => {
        impl FromValue for $ty {
            fn from_value(v: Value) -> Result<$ty, ExecError> {
                match v {
                    Value::Integer(ref i) => i.$meth().ok_or(ExecError::Overflow),
                    ref v => Err(ExecError::expected("integer", v))
                }
            }
        }
    }
}

simple_from_value!{ (); "unit"; Value::Unit => () }
simple_from_value!{ bool; "bool"; Value::Bool(b) => b }
simple_from_value!{ char; "char"; Value::Char(ch) => ch }
simple_from_value!{ f32; "float"; Value::Float(f) => f as f32 }
simple_from_value!{ f64; "float"; Value::Float(f) => f }
simple_from_value!{ String; "string"; Value::String(s) => s }
simple_from_value!{ Integer; "integer"; Value::Integer(i) => i }
simple_from_value!{ Ratio; "ratio"; Value::Ratio(r) => r }

integer_from_value!{ i8 to_i8 }
integer_from_value!{ i16 to_i16 }
integer_from_value!{ i32 to_i32 }
integer_from_value!{ i64 to_i64 }
integer_from_value!{ isize to_isize }
integer_from_value!{ u8 to_u8 }
integer_from_value!{ u16 to_u16 }
integer_from_value!{ u32 to_u32 }
integer_from_value!{ u64 to_u64 }
integer_from_value!{ usize to_usize }

impl FromValue for Value {
    #[inline]
    fn from_value(v: Value) -> Result<Value, ExecError> {
        Ok(v)
    }
}

impl FromValue for Lambda {
    fn from_value(v: Value) -> Result<Lambda, ExecError> {
        match v {
            Value::Lambda(l) => Ok(l),
            ref v => Err(ExecError::expected("lambda", v))
        }
    }
}

impl<T: FromValue> FromValue for Vec<T> {
    fn from_value(v: Value) -> Result<Vec<T>, ExecError> {
        match v {
            Value::Unit => Ok(Vec::new()),
            Value::List(li) => li.into_vec().into_iter()
                .map(T::from_value).collect(),
            ref v => Err(ExecError::expected("list", v))
        }
    }
}

macro_rules! value_from {
    ( $ty:ty ; $pat:pat => $expr:expr ) => {
        impl From<$ty> for Value {
            fn from($pat: $ty) -> Value {
                $expr
            }
        }
    }
}

value_from!{ (); _ => Value::Unit }
value_from!{ bool; b => Value::Bool(b) }
value_from!{ char; c => Value::Char(c) }
value_from!{ Integer; i => Value::Integer(i) }
value_from!{ Ratio; r => Value::Ratio(r) }
value_from!{ String; s => Value::String(s) }
value_from!{ f32; f => Value::Float(f as f64) }
value_from!{ f64; f => Value::Float(f) }

impl<'a> From<&'a str> for Value {
    fn from(s: &str) -> Value {
        s.to_owned().into()
    }
}

impl<T: Into<Value>> From<Vec<T>> for Value {
    fn from(v: Vec<T>) -> Value {
        if v.is_empty() {
            Value::Unit
        } else {
            Value::List(RcVec::new(v.into_iter().map(|v| v.into()).collect()))
        }
    }
}

impl<'a, T: Clone + Into<Value>> From<&'a [T]> for Value {
    fn from(v: &[T]) -> Value {
        if v.is_empty() {
            Value::Unit
        } else {
            Value::List(RcVec::new(v.iter().map(|v| v.clone().into()).collect()))
        }
    }
}

impl<'a, T: Clone + Into<Value>> From<&'a mut [T]> for Value {
    fn from(v: &mut [T]) -> Value {
        (&*v).into()
    }
}

impl From<RcVec<Value>> for Value {
    fn from(v: RcVec<Value>) -> Value {
        if v.is_empty() {
            Value::Unit
        } else {
            Value::List(v)
        }
    }
}

macro_rules! from_integer {
    ( $ty:ident $meth:ident ) => {
        impl From<$ty> for Value {
            fn from(i: $ty) -> Value {
                Value::Integer(Integer::$meth(i))
            }
        }
    }
}

from_integer!{ i8 from_i8 }
from_integer!{ i16 from_i16 }
from_integer!{ i32 from_i32 }
from_integer!{ i64 from_i64 }
from_integer!{ isize from_isize }
from_integer!{ u8 from_u8 }
from_integer!{ u16 from_u16 }
from_integer!{ u32 from_u32 }
from_integer!{ u64 from_u64 }
from_integer!{ usize from_usize }

macro_rules! conv_tuple {
    ( $n:expr => $( $name:ident )+ ) => {
        impl<$( $name: Into<Value> ),+> From<( $( $name ),+ ,)> for Value {
            #[allow(non_snake_case)]
            fn from(v: ( $( $name , )+ )) -> Value {
                let ( $( $name , )+ ) = v;

                vec![$( $name.into() ),+].into()
            }
        }

        impl<$( $name: FromValue ),+> FromValue for ( $( $name , )+ ) {
            fn from_value(v: Value) -> Result<( $( $name , )+ ), ExecError> {
                match v {
                    Value::List(ref li) if li.len() == $n => (),
                    ref v => return Err(ExecError::expected(
                        concat!("list of ", stringify!($n), " elements"), v))
                }

                let mut iter = match v {
                    Value::List(li) => li.into_vec().into_iter(),
                    _ => unreachable!()
                };

                Ok((
                    $( try!($name::from_value(iter.next().unwrap())) , )+
                ))
            }
        }

        impl<'a, $( $name: FromValueRef<'a> ),+> FromValueRef<'a> for ( $( $name , )+ ) {
            fn from_value_ref(v: &'a Value) -> Result<( $( $name , )+ ), ExecError> {
                let mut iter = match *v {
                    Value::List(ref li) if li.len() == $n => li.iter(),
                    _ => return Err(ExecError::expected(
                        concat!("list of ", stringify!($n), " elements"), v))
                };

                Ok((
                    $( try!($name::from_value_ref(iter.next().unwrap())) , )+
                ))
            }
        }
    }
}

conv_tuple!{  1 => A }
conv_tuple!{  2 => A B }
conv_tuple!{  3 => A B C }
conv_tuple!{  4 => A B C D }
conv_tuple!{  5 => A B C D E }
conv_tuple!{  6 => A B C D E F }
conv_tuple!{  7 => A B C D E F G }
conv_tuple!{  8 => A B C D E F G H }
conv_tuple!{  9 => A B C D E F G H I }
conv_tuple!{ 10 => A B C D E F G H I J }
conv_tuple!{ 11 => A B C D E F G H I J K }
conv_tuple!{ 12 => A B C D E F G H I J K L }

/// Represents a structure value containing named fields
#[derive(Clone, Debug)]
pub struct Struct {
    /// Struct definition
    pub def: Rc<StructDef>,
    /// Struct fields
    pub fields: NameMapSlice<Value>,
}

impl Struct {
    /// Creates a new `Struct` value with the given `StructDef` and field values.
    pub fn new(def: Rc<StructDef>, fields: NameMapSlice<Value>) -> Struct {
        Struct{
            def: def,
            fields: fields,
        }
    }

    /// Returns the value for the named field, if present.
    pub fn get_field(&self, name: Name) -> Option<&Value> {
        self.fields.get(name)
    }
}

/// Represents the definition of a class of struct value
#[derive(Clone, Debug)]
pub struct StructDef {
    /// Struct name
    pub name: Name,
    /// Struct fields, mapped to names of expected types
    // TODO: Name-based type-checking prevents a StructDef from requiring
    // a specific class of Struct value for a field.
    pub fields: NameMapSlice<Name>,
}

impl PartialEq for StructDef {
    fn eq(&self, rhs: &StructDef) -> bool {
        (self as *const _) == (rhs as *const _)
    }
}

impl StructDef {
    /// Creates a new `StructDef` with the given name and fields.
    pub fn new(name: Name, fields: NameMapSlice<Name>) -> StructDef {
        StructDef{
            name: name,
            fields: fields,
        }
    }
}

#[cfg(test)]
mod test {
    use exec::ExecError;
    use super::ForeignValue;

    #[derive(Debug)]
    struct Dummy {
        a: i32,
    }

    impl ForeignValue for Dummy {
        fn type_name(&self) -> &'static str { panic!() }
    }

    #[test]
    fn test_foreign_value() {
        let mut a: Box<ForeignValue> = Box::new(Dummy{a: 0});

        {
            let mut r = a.downcast_mut::<Dummy>().unwrap();
            r.a = 123;
        }

        let r = a.downcast_ref::<Dummy>().unwrap();

        assert_eq!(r.a, 123);
    }
}
