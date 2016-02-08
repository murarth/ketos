extern crate ketos;

use ketos::{ExecError, FromValue, FromValueRef, Value};

macro_rules! assert_matches {
    ( $e:expr, $pat:pat ) => {
        match $e {
            $pat => (),
            e => panic!("assertion failed: `{:?}` does not match `{}`",
                e, stringify!($pat))
        }
    };
    ( $e:expr, $pat:pat if $cond:expr ) => {
        match $e {
            $pat if $cond => (),
            e => panic!("assertion failed: `{:?}` does not match `{} if {}`",
                e, stringify!($pat), stringify!($cond))
        }
    }
}

fn from<T: FromValue>(v: Value) -> Result<T, ExecError> {
    T::from_value(v)
}

fn from_ref<'a, T: FromValueRef<'a>>(v: &'a Value) -> Result<T, ExecError> {
    T::from_value_ref(v)
}

fn into<T: Into<Value>>(t: T) -> Value {
    t.into()
}

#[test]
fn test_from_value() {
    assert_eq!(from::<()>(Value::Unit).unwrap(), ());
    assert_eq!(from::<i32>(into(123)).unwrap(), 123);
    assert_eq!(from::<String>(into("foo")).unwrap(), "foo");

    assert_eq!(from::<Vec<i32>>(Value::Unit).unwrap(), vec![]);
    assert_eq!(from::<Vec<i32>>(into(vec![1, 2, 3])).unwrap(), vec![1, 2, 3]);
}

#[test]
fn test_from_value_ref() {
    assert_eq!(from_ref::<()>(&Value::Unit).unwrap(), ());
    assert_eq!(from_ref::<i32>(&into(456)).unwrap(), 456);
    assert_eq!(from_ref::<&str>(&into("foo")).unwrap(), "foo");
    assert_eq!(from_ref::<Vec<i32>>(&into(vec![1, 2, 3])).unwrap(), vec![1, 2, 3]);
}

#[test]
fn test_into_value() {
    assert_matches!(into(()), Value::Unit);
    assert_matches!(into(true), Value::Bool(true));
    assert_matches!(into(1.0_f64), Value::Float(1.0));
    assert_matches!(into(123),
        Value::Integer(ref i) if i.to_u32() == Some(123));
    assert_matches!(into("foo"), Value::String(ref s) if s == "foo");

    assert_matches!(into(Vec::<i32>::new()), Value::Unit);
    assert_matches!(into(Vec::<Value>::new()), Value::Unit);
}
