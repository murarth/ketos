extern crate ketos;
#[macro_use] extern crate ketos_derive;

use std::fmt;

use ketos::{FromValue, FromValueRef, Value};

#[derive(Debug, ForeignValue, FromValue, FromValueRef, IntoValue)]
struct NoClone(&'static str);

#[derive(Clone, Debug, ForeignValue, FromValueClone, FromValueRef, IntoValue)]
struct Cloner(&'static str);

#[test]
fn test_derive() {
    let a: Value = NoClone("foo").into();
    let b = a.clone();

    assert!(<&NoClone>::from_value_ref(&a).is_ok());
    assert!(NoClone::from_value(a).is_err());
    assert!(NoClone::from_value(b).is_ok());

    let a: Value = Cloner("foo").into();
    let b = a.clone();

    assert!(<&Cloner>::from_value_ref(&a).is_ok());
    assert!(Cloner::from_value(a).is_ok());
    assert!(Cloner::from_value(b).is_ok());
}

#[derive(ForeignValue, FromValue, FromValueRef, IntoValue)]
struct Generic<T: 'static>(T);

impl<T> fmt::Debug for Generic<T> {
    fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result { unimplemented!() }
}

#[derive(ForeignValue, FromValue, FromValueRef, IntoValue)]
struct GenericWhere<T>(T) where T: 'static;

impl<T> fmt::Debug for GenericWhere<T> {
    fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result { unimplemented!() }
}

#[derive(ForeignValue, FromValueClone, FromValueRef, IntoValue)]
struct CloneGeneric<T: 'static>(T);

impl<T> Clone for CloneGeneric<T> {
    fn clone(&self) -> Self { unimplemented!() }
}

impl<T> fmt::Debug for CloneGeneric<T> {
    fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result { unimplemented!() }
}

#[derive(ForeignValue, FromValueClone, FromValueRef, IntoValue)]
struct CloneGenericWhere<T>(T) where T: 'static;

impl<T> Clone for CloneGenericWhere<T> {
    fn clone(&self) -> Self { unimplemented!() }
}

impl<T> fmt::Debug for CloneGenericWhere<T> {
    fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result { unimplemented!() }
}
