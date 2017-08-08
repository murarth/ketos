extern crate ketos;

use ketos::{Error, Interpreter, Value};
use ketos::bytecode::Instruction;
use ketos::bytecode::Instruction::*;
use ketos::name::standard_names;

fn lambda(s: &str) -> Result<Vec<Instruction>, Error> {
    let interp = Interpreter::new();
    let _exprs = try!(interp.compile_exprs(s));

    match interp.scope().get_named_value("test") {
        Some(Value::Lambda(ref l)) => Ok(l.code.instructions.clone().into_vec()),
        Some(ref v) => panic!("expected lambda; got {}", v.type_name()),
        None => panic!("missing `test` function")
    }
}

#[test]
fn test_const() {
    assert_eq!(lambda("
        (const c (+ 1 2 3))
        (define (test) c)
        ").unwrap(), [
            Const(0),
            Return,
        ]);
}

#[test]
fn test_const_if() {
    assert_eq!(lambda("(define (test a) (if true (+ a) (- a)))").unwrap(), [
        LoadPush(0),
        CallSysArgs(standard_names::ADD.get(), 1),
        Return,
    ]);

    assert_eq!(lambda("(define (test a) (if false (+ a) (- a)))").unwrap(), [
        LoadPush(0),
        CallSysArgs(standard_names::SUB.get(), 1),
        Return,
    ]);
}

#[test]
fn test_const_fold() {
    assert_eq!(lambda("(define (test a) (+ a 0))").unwrap(), [
        LoadPush(0),
        CallSysArgs(standard_names::ADD.get(), 1),
        Return,
    ]);

    assert_eq!(lambda("(define (test a) (+ 0 a))").unwrap(), [
        LoadPush(0),
        CallSysArgs(standard_names::ADD.get(), 1),
        Return,
    ]);

    assert_eq!(lambda("(define (test a) (- a 0))").unwrap(), [
        LoadPush(0),
        CallSysArgs(standard_names::ADD.get(), 1),
        Return,
    ]);

    assert_eq!(lambda("(define (test a) (- 0 a))").unwrap(), [
        LoadPush(0),
        CallSysArgs(standard_names::SUB.get(), 1),
        Return,
    ]);

    assert_eq!(lambda("(define (test a) (// 1 a))").unwrap(), [
        LoadPush(0),
        CallSysArgs(standard_names::FLOOR_DIV.get(), 1),
        Return,
    ]);

    assert_eq!(lambda("(define (test a) (// a 1))").unwrap(), [
        LoadPush(0),
        CallSys(standard_names::FLOOR.get()),
        Return,
    ]);
}

#[test]
fn test_dec() {
    assert_eq!(lambda("(define (test a) (- a 1))").unwrap(), [
        Load(0),
        Dec,
        Return,
    ]);

    assert_eq!(lambda("
        (const n 1)
        (define (test a) (- a n))
        ").unwrap(), [
            Load(0),
            Dec,
            Return,
        ]);

    assert_eq!(lambda("(define (test a) (+ a -1))").unwrap(), [
        Load(0),
        Dec,
        Return,
    ]);

    assert_eq!(lambda("(define (test a) (+ -1 a))").unwrap(), [
        Load(0),
        Dec,
        Return,
    ]);
}

#[test]
fn test_inc() {
    assert_eq!(lambda("(define (test a) (+ a 1))").unwrap(), [
        Load(0),
        Inc,
        Return,
    ]);

    assert_eq!(lambda("
        (const n 1)
        (define (test a) (+ a n))
        ").unwrap(), [
            Load(0),
            Inc,
            Return,
        ]);

    assert_eq!(lambda("(define (test a) (+ 1 a))").unwrap(), [
        Load(0),
        Inc,
        Return,
    ]);

    assert_eq!(lambda("(define (test a) (- a -1))").unwrap(), [
        Load(0),
        Inc,
        Return,
    ]);
}

#[test]
fn test_if() {
    assert_eq!(lambda("(define (test a b c) (if a b c))").unwrap(), [
        Load(0),
        JumpIfNot(4),
        Load(1),
        Return,
        Load(2),
        Return,
    ]);

    assert_eq!(lambda("(define (test a b c) (if (not a) b c))").unwrap(), [
        Load(0),
        JumpIf(4),
        Load(1),
        Return,
        Load(2),
        Return,
    ]);
}

#[test]
fn test_lambda() {
    assert_eq!(lambda("(define (test a b) (+ a b))").unwrap(), [
        LoadPush(0),
        LoadPush(1),
        CallSysArgs(standard_names::ADD.get(), 2),
        Return,
    ]);
}

#[test]
fn test_call_self() {
    assert_eq!(lambda("(define (test a) (do (test a) ()))").unwrap(), [
        LoadPush(0),
        CallSelf(1),
        Unit,
        Return,
    ]);

    // Prevents self-call in case one wants to do something tricky.
    assert_eq!(lambda("(define (test a) (do ((id test) a) ()))").unwrap(), [
        GetDefPush(0),
        LoadPush(0),
        Call(1),
        Unit,
        Return,
    ]);
}

#[test]
fn test_tail_recursion() {
    assert_eq!(lambda("(define (test a) (test a))").unwrap(), [
        LoadPush(0),
        TailCallSelf(1),
    ]);

    assert_eq!(lambda("(define (test a)
                         (if (something a)
                            (test 1)
                            (test 2)))").unwrap(), [
        LoadPush(0),
        CallConst(0, 1),
        JumpIfNot(5),
        ConstPush(1),
        TailCallSelf(1),
        ConstPush(2),
        TailCallSelf(1),
    ]);

    assert_eq!(lambda("(define (test) (and a (test)))").unwrap(), [
        GetDef(0),
        JumpIfNot(3),
        TailCallSelf(0),
        Return,
    ]);

    assert_eq!(lambda("(define (test) (let ((a 1)) (test)))").unwrap(), [
        ConstPush(0),
        TailCallSelf(0),
    ]);
}

#[test]
fn test_tail_recursion_apply() {
    assert_eq!(lambda("(define (test a) (apply test a))").unwrap(), [
        Load(0),
        TailApplySelf(0),
    ]);

    assert_eq!(lambda("(define (test a)
                         (if (something a)
                            (apply test ())
                            (apply test ())))").unwrap(), [
        LoadPush(0),
        CallConst(0, 1),
        JumpIfNot(5),
        Unit,
        TailApplySelf(0),
        Unit,
        TailApplySelf(0),
    ]);

    assert_eq!(lambda("(define (test) (and a (apply test ())))").unwrap(), [
        GetDef(0),
        JumpIfNot(4),
        Unit,
        TailApplySelf(0),
        Return,
    ]);

    assert_eq!(lambda("(define (test) (let ((a 1)) (apply test ())))").unwrap(), [
        ConstPush(0),
        Unit,
        TailApplySelf(0),
    ]);
}
