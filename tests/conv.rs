#[macro_use]
extern crate assert_matches;

extern crate ketos;

use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

use ketos::{Bytes, ExecError, FromValue, FromValueRef, Value};

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
    assert_eq!(
        from::<Vec<i32>>(into(vec![1, 2, 3])).unwrap(),
        vec![1, 2, 3]
    );

    assert_eq!(
        from::<(String, i32)>(into(("foo", 1))).unwrap(),
        ("foo".to_owned(), 1)
    );

    assert_eq!(from::<PathBuf>(into("foo")).unwrap(), PathBuf::from("foo"));
    assert_eq!(
        from::<PathBuf>(into(Path::new("foo"))).unwrap(),
        PathBuf::from("foo")
    );
    assert_eq!(
        from::<OsString>(into("foo")).unwrap(),
        OsString::from("foo")
    );
    assert_eq!(
        from::<OsString>(into(Path::new("foo"))).unwrap(),
        OsString::from("foo")
    );
    assert_eq!(
        from::<Bytes>(into(Bytes::from("foo"))).unwrap(),
        Bytes::from("foo")
    );
}

#[test]
fn test_from_value_ref() {
    assert_eq!(from_ref::<()>(&Value::Unit).unwrap(), ());
    assert_eq!(from_ref::<i32>(&into(456)).unwrap(), 456);
    assert_eq!(from_ref::<&str>(&into("foo")).unwrap(), "foo");
    assert_eq!(
        from_ref::<Vec<i32>>(&into(vec![1, 2, 3])).unwrap(),
        vec![1, 2, 3]
    );

    assert_eq!(
        from_ref::<(&str, i32)>(&into(("foo", 1))).unwrap(),
        ("foo", 1)
    );

    assert_eq!(from_ref::<&Path>(&into("foo")).unwrap(), Path::new("foo"));
    assert_eq!(
        from_ref::<&Path>(&into(Path::new("foo"))).unwrap(),
        Path::new("foo")
    );
    assert_eq!(from_ref::<&OsStr>(&into("foo")).unwrap(), OsStr::new("foo"));
    assert_eq!(
        from_ref::<&OsStr>(&into(Path::new("foo"))).unwrap(),
        OsStr::new("foo")
    );
    assert_eq!(
        from_ref::<&Bytes>(&into(Bytes::from("foo"))).unwrap(),
        &Bytes::from("foo")
    );
    assert_eq!(
        from_ref::<&[u8]>(&into(Bytes::from("foo"))).unwrap(),
        b"foo"
    );
}

#[test]
fn test_into_value() {
    assert_matches!(into(()), Value::Unit);
    assert_matches!(into(true), Value::Bool(true));
    assert_matches!(into(1.0_f64), Value::Float(f) if f == 1.0);
    assert_matches!(into(123),
        Value::Integer(ref i) if i.to_u32() == Some(123));
    assert_matches!(into("foo"), Value::String(ref s) if s == "foo");
    assert_matches!(into((1, 2)), Value::List(ref li) if li.len() == 2);

    assert_matches!(into(Vec::<i32>::new()), Value::Unit);
    assert_matches!(into(Vec::<Value>::new()), Value::Unit);
}
