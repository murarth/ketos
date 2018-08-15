#![cfg(all(feature = "serde", feature = "serde_derive"))]

extern crate ketos;
extern crate serde;
#[macro_use] extern crate serde_derive;

use std::collections::BTreeMap;
use std::path::PathBuf;

use ketos::{
    BuiltinModuleLoader, FileModuleLoader, ModuleLoader,
    Error, Interpreter, decode_value, encode_value,
};

macro_rules! map {
    ( $( $k:expr => $v:expr ),* ) => { {
        let mut _m = BTreeMap::new();
        $( _m.insert($k, $v); )*
        _m
    } }
}

macro_rules! test {
    ( $a:expr , $b:expr ) => { {
        let interp = interp(&format!(r#"
            (define (give v)
              (assert-eq v '{0}))
            (define (take) '{0})
            "#, $b)).unwrap();

        let v = $a;

        interp.call("give", vec![
            encode_value(interp.scope(), &v).unwrap(),
        ]).unwrap();

        let v2 = decode_value(interp.scope(),
            &interp.call("take", vec![]).unwrap()).unwrap();

        assert_eq!(v, v2);
    } }
}

fn interp(code: &str) -> Result<Interpreter, Error> {
    let mut loader = FileModuleLoader::with_search_paths(vec![PathBuf::from("lib")]);

    loader.set_read_bytecode(false);
    loader.set_write_bytecode(false);

    let interp = Interpreter::with_loader(
        Box::new(BuiltinModuleLoader.chain(loader)));

    interp.run_code("(use test (assert-eq))", None)?;
    interp.run_code(code, None)?;

    Ok(interp)
}

#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
struct StructA {
    a: i32,
    b: char,
    c: String,
}

const STRUCT_0: &'static str =
    r#"(StructA (:a 123 :b #'x' :c "foo"))"#;

fn struct_0() -> StructA {
    StructA{
        a: 123,
        b: 'x',
        c: "foo".to_owned(),
    }
}

#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
struct StructB {
    a: Vec<i32>,
    b: BTreeMap<String, String>,
}

const STRUCT_1: &'static str =
    r#"(StructB (:a () :b ()))"#;

fn struct_1() -> StructB {
    StructB{
        a: vec![],
        b: map!(),
    }
}

const STRUCT_2: &'static str =
    r#"(StructB (:a (1 2 3) :b (("a" "b") ("c" "d"))))"#;

fn struct_2() -> StructB {
    StructB{
        a: vec![1, 2, 3],
        b: map!("a".to_owned() => "b".to_owned(), "c".to_owned() => "d".to_owned()),
    }
}

#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
struct StructC(u8, (u16, u32), [i32; 2]);

const STRUCT_3: &'static str =
    "(StructC (1 (2 3) (4 5)))";

fn struct_3() -> StructC {
    StructC(1, (2, 3), [4, 5])
}

#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
struct StructD;

const STRUCT_4: &'static str =
    "(StructD ())";

fn struct_4() -> StructD { StructD }

#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
struct StructE {
    a: StructA,
    b: StructB,
    c: StructC,
    d: StructD,
}

const STRUCT_5: &'static str =
    r#"(StructE (:a (StructA (:a -1 :b #'.' :c "lol"))
                 :b (StructB (:a (0) :b (("a" "b"))))
                 :c (StructC (2 (1 0) (-1 -2)))
                 :d (StructD ())))"#;

fn struct_5() -> StructE {
    StructE{
        a: StructA{a: -1, b: '.', c: "lol".to_owned()},
        b: StructB{a: vec![0], b: map!("a".to_owned() => "b".to_owned())},
        c: StructC(2, (1, 0), [-1, -2]),
        d: StructD,
    }
}

#[test]
fn test_struct() {
    test!(struct_0(), STRUCT_0);
    test!(struct_1(), STRUCT_1);
    test!(struct_2(), STRUCT_2);
    test!(struct_3(), STRUCT_3);
    test!(struct_4(), STRUCT_4);
    test!(struct_5(), STRUCT_5);
}

#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
enum Enum {
    Alpha,
    Beta(i32),
    Gamma(char, ()),
    Delta{a: String, b: u32},
}

const ENUM_0: &'static str =
    "(Enum Alpha ())";

fn enum_0() -> Enum {
    Enum::Alpha
}

const ENUM_1: &'static str =
    "(Enum Beta (1))";

fn enum_1() -> Enum {
    Enum::Beta(1)
}

const ENUM_2: &'static str =
    "(Enum Gamma (#'a' ()))";

fn enum_2() -> Enum {
    Enum::Gamma('a', ())
}

const ENUM_3: &'static str =
    r#"(Enum Delta (:a "foo" :b 123))"#;

fn enum_3() -> Enum {
    Enum::Delta{a: "foo".to_owned(), b: 123}
}

#[test]
fn test_enum() {
    test!(enum_0(), ENUM_0);
    test!(enum_1(), ENUM_1);
    test!(enum_2(), ENUM_2);
    test!(enum_3(), ENUM_3);
}

macro_rules! de {
    ( $ty:ty => $e:expr ) => { {
        let interp = interp(&format!("
            (define (make) '{})
            ", $e)).unwrap();

        decode_value::<$ty>(interp.scope(),
            &interp.call("make", vec![]).unwrap())
    } }
}

#[test]
fn test_primitive() {
    assert_eq!(de!((u32, String) => r#"(1 "foo")"#).unwrap(),
        (1, "foo".to_owned()));
    assert_eq!(de!(Vec<u32> => "(1 2 3)").unwrap(), [1, 2, 3]);
    assert_eq!(de!(BTreeMap<u32, u32> => "((1 2) (3 4))").unwrap(),
        map!(1 => 2, 3 => 4));
}

#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
struct OptStruct {
    a: Option<i32>,
}

#[test]
fn test_option() {
    assert_eq!(de!(Option<i32> => "()").unwrap(), None);
    assert_eq!(de!(Option<i32> => "1").unwrap(), Some(1));

    assert_eq!(de!(OptStruct => "(OptStruct (:a 1))").unwrap(),
        OptStruct{a: Some(1)});
    assert_eq!(de!(OptStruct => "(OptStruct (:a ()))").unwrap(),
        OptStruct{a: None});
}

#[test]
fn test_error() {
    assert!(de!(StructA => "0").is_err());
    assert!(de!(StructA => "()").is_err());
    assert!(de!(StructA => "(StructA)").is_err());
    assert!(de!(StructA => "(StructA ())").is_err());
    assert!(de!(StructA => "(StructA () ())").is_err());
    assert!(de!(StructA => "(StructB (:a ()))").is_err());
    assert!(de!(StructA => "(StructB (:a () :b () :c ()))").is_err());

    assert!(de!(Enum => "0").is_err());
    assert!(de!(Enum => "()").is_err());
    assert!(de!(Enum => "(Enum)").is_err());
    assert!(de!(Enum => "(Enum Alpha)").is_err());
    assert!(de!(Enum => "(Enum Alpha (0))").is_err());
    assert!(de!(Enum => "(Enum Alpha () ())").is_err());
    assert!(de!(Enum => "(Enum Gamma (#'x'))").is_err());
    assert!(de!(Enum => "(Enum Lol ())").is_err());

    assert!(de!(BTreeMap<u32, u32> => "((0 1) ())").is_err());
    assert!(de!(BTreeMap<u32, u32> => "((0 1) (1))").is_err());
    assert!(de!(BTreeMap<u32, u32> => "((0 1) (1 2 3))").is_err());
    assert!(de!(Vec<u32> => "(1 2 ())").is_err());
}
