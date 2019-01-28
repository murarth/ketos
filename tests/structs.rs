#[macro_use] extern crate assert_matches;

extern crate ketos;
#[macro_use] extern crate ketos_derive;

use ketos::{Error, ExecError, FromValue, Interpreter, Value};

#[derive(Clone, Debug, ForeignValue, StructValue)]
struct Foo {
    name: String,
    num: u32,
}

#[derive(Clone, Debug, ForeignValue, StructValue)]
struct Bar {
    name: String,
    num: u32,
}

fn interp() -> Interpreter {
    let interp = Interpreter::default();

    interp.scope().register_struct_value::<Foo>();
    interp.scope().register_struct_value::<Bar>();

    interp
}

fn eval(interp: &Interpreter, code: &str) -> Result<Value, Error> {
    interp.run_code(code, None)
}

fn conv<T: FromValue>(interp: &Interpreter, code: &str) -> Result<T, Error> {
    let v = eval(interp, code)?;
    let t = T::from_value(v)?;
    Ok(t)
}

#[test]
fn test_struct() {
    let interp = interp();

    eval(&interp, r#"(define foo (new Foo :name "foo" :num 123))"#).unwrap();

    assert_eq!(conv::<String>(&interp, "(. foo :name)").unwrap(), "foo");
    assert_eq!(conv::<u32>(&interp, "(. foo :num)").unwrap(), 123);

    assert_matches!(eval(&interp, "(. foo :lolwut)").unwrap_err(),
        Error::ExecError(ExecError::FieldError{..}));

    eval(&interp, r#"(define bar (.= foo :name "bar"))"#).unwrap();

    assert_eq!(conv::<String>(&interp, "(. bar :name)").unwrap(), "bar");
    assert_eq!(conv::<u32>(&interp, "(. bar :num)").unwrap(), 123);

    assert_eq!(conv::<bool>(&interp, "(is-instance Foo foo)").unwrap(), true);
    assert_eq!(conv::<bool>(&interp, "(is-instance Bar foo)").unwrap(), false);
}
