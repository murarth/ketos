#[macro_use] extern crate assert_matches;

#[macro_use] extern crate ketos;

use std::cmp::Ordering;

use ketos::{Context, ExecError, Error, ForeignValue, Interpreter, Value};

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct MyType {
    a: i32,
}

impl ketos::ForeignValue for MyType {
    fn compare_to(&self, rhs: &ForeignValue) -> Result<Ordering, ExecError> {
        match rhs.downcast_ref::<MyType>() {
            Some(rhs) => Ok(self.cmp(rhs)),
            None => Err(ExecError::TypeMismatch{
                lhs: self.type_name(),
                rhs: rhs.type_name(),
            })
        }
    }

    fn is_equal_to(&self, rhs: &ForeignValue) -> Result<bool, ExecError> {
        match rhs.downcast_ref::<MyType>() {
            Some(rhs) => Ok(*self == *rhs),
            None => Err(ExecError::TypeMismatch{
                lhs: self.type_name(),
                rhs: rhs.type_name(),
            })
        }
    }

    fn type_name(&self) -> &'static str { "my-type" }
}

foreign_type_conversions!{ MyType => "my-type" }

fn eval(interp: &Interpreter, input: &str) -> Result<String, Error> {
    let v = try!(interp.run_single_expr(input, None));
    Ok(interp.format_value(&v))
}

#[test]
fn test_foreign_value() {
    let interp = Interpreter::new();

    interp.scope().add_named_value(
        "my-value", Value::new_foreign(MyType{a: 123}));

    assert_eq!(eval(&interp, "my-value").unwrap(), "MyType { a: 123 }");
    assert_eq!(eval(&interp, "(type-of my-value)").unwrap(), "my-type");
    assert_eq!(eval(&interp, "(is 'my-type my-value)").unwrap(), "true");
}

fn reflect_args(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    Ok(args.into())
}

#[test]
fn test_raw_foreign_fn() {
    let interp = Interpreter::new();

    interp.scope().add_value_with_name("reflect-args",
        |name| Value::new_foreign_fn(name, reflect_args));

    assert_eq!(eval(&interp, "(reflect-args 1 2 3)").unwrap(), "(1 2 3)");

    interp.scope().add_value_with_name("closure-args",
        |name| Value::new_foreign_fn(name, |_scope, args| Ok(args.into())));

    assert_eq!(eval(&interp, "(closure-args 3 2 1)").unwrap(), "(3 2 1)");
}

fn new_my_type(a: i32) -> Result<MyType, Error> {
    Ok(MyType{a: a})
}

fn get_value(a: &MyType) -> Result<i32, Error> {
    Ok(a.a)
}

fn add_pairs(a: (i32, i32), b: (i32, i32)) -> Result<(i32, i32), Error> {
    Ok((a.0 + b.0, a.1 + b.1))
}

fn hello(s: &str) -> Result<String, Error> {
    Ok(format!("Hello, {}!", s))
}

#[test]
fn test_foreign_fn() {
    let interp = Interpreter::new();
    let scope = interp.scope();

    ketos_fn!{ scope => "new-my-type" => fn new_my_type(a: i32) -> MyType }
    ketos_fn!{ scope => "get-value" => fn get_value(a: &MyType) -> i32 }
    ketos_fn!{ scope => "add-pairs" => fn add_pairs(a: (i32, i32), b: (i32, i32)) -> (i32, i32) }
    ketos_fn!{ scope => "hello" => fn hello(s: &str) -> String }

    assert_eq!(eval(&interp, "(new-my-type 1)").unwrap(), "MyType { a: 1 }");
    assert_eq!(eval(&interp, "(get-value (new-my-type 2))").unwrap(), "2");
    assert_eq!(eval(&interp, "(add-pairs '(1 2) '(3 4))").unwrap(), "(4 6)");
    assert_eq!(eval(&interp, r#"(hello "world")"#).unwrap(), r#""Hello, world!""#);

    assert_matches!(eval(&interp, "(add-pairs '(1 2 0) '(3 4))").unwrap_err(),
        Error::ExecError(ExecError::TypeError{..}));
}
