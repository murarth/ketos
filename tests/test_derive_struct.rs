extern crate ketos;
#[macro_use] extern crate ketos_derive;

use ketos::{FromValue, Interpreter};

#[derive(Clone, Debug, FromValueClone, ForeignValue, IntoValue, StructValue)]
struct Foo {
    name: String,
    value: i32,
}

#[derive(Clone, Debug, FromValueClone, ForeignValue, IntoValue, StructValue)]
struct Bar {
    name_with_underscore: String,
}

#[derive(Clone, Debug, FromValueClone, ForeignValue, IntoValue, StructValue)]
struct Baz {
    #[ketos(rename = "ketos-name")]
    rust_name: String,
}

#[derive(Clone, Debug, FromValueClone, ForeignValue, IntoValue, StructValue)]
struct Quux {
    foo: Foo,
    bar: Bar,
    baz: Baz,
}

#[test]
fn test_derive_struct() {
    let interp = Interpreter::new();

    interp.scope().register_struct_value::<Foo>();

    let v = interp.run_code(r#"
        (new Foo :name "hello" :value 123)
        "#, None).unwrap();

    let foo = Foo::from_value(v).unwrap();

    assert_eq!(foo.name, "hello");
    assert_eq!(foo.value, 123);
}

#[test]
fn test_derive_struct_name() {
    let interp = Interpreter::new();

    interp.scope().register_struct_value::<Bar>();

    let v = interp.run_code(r#"
        (new Bar :name-with-underscore "foo")
        "#, None).unwrap();

    let bar = Bar::from_value(v).unwrap();

    assert_eq!(bar.name_with_underscore, "foo");
}

#[test]
fn test_derive_struct_rename() {
    let interp = Interpreter::new();

    interp.scope().register_struct_value::<Baz>();

    let v = interp.run_code(r#"
        (new Baz :ketos-name "foo")
        "#, None).unwrap();

    let baz = Baz::from_value(v).unwrap();

    assert_eq!(baz.rust_name, "foo");
}

#[test]
fn test_derive_struct_in_struct() {
    let interp = Interpreter::new();

    interp.scope().register_struct_value::<Foo>();
    interp.scope().register_struct_value::<Bar>();
    interp.scope().register_struct_value::<Baz>();
    interp.scope().register_struct_value::<Quux>();

    let v = interp.run_code(r#"
        (new Quux
            :foo (new Foo :name "foo" :value 0)
            :bar (new Bar :name-with-underscore "bar")
            :baz (new Baz :ketos-name "baz"))
        "#, None).unwrap();

    let quux = Quux::from_value(v).unwrap();

    assert_eq!(quux.foo.name, "foo");
    assert_eq!(quux.bar.name_with_underscore, "bar");
    assert_eq!(quux.baz.rust_name, "baz");
}
