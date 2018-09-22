#![feature(test)]

extern crate ketos;
extern crate test;

use std::rc::Rc;

use test::Bencher;

use ketos::{Code, Error, Interpreter};

fn compile(setup: &str, input: &str) -> Result<(Interpreter, Rc<Code>), Error> {
    let interp = Interpreter::new();

    let _ = interp.run_code(setup, None)?;
    let code = interp.compile_single_expr(input, None)?;

    Ok((interp, Rc::new(code)))
}

fn run_bench(b: &mut Bencher, setup: &str, input: &str) {
    let (interp, code) = compile(setup, input).unwrap();

    b.iter(|| interp.execute_code(code.clone()).unwrap());
}

fn factorial(b: &mut Bencher, n: u32) {
    run_bench(
        b,
        r#"
        (define (factorial n) (fac-recursive n 1))

        (define (fac-recursive n acc)
          (if (<= n 1)
            acc
            (fac-recursive (- n 1) (* n acc))))
        "#,
        &format!("(factorial {})", n),
    );
}

fn fib(b: &mut Bencher, n: u32) {
    run_bench(
        b,
        r#"
        (define (fib n) (fib-recursive n 0 1))

        (define (fib-recursive n a b)
          (if (= n 0)
            a
            (fib-recursive (- n 1) b (+ a b))))
        "#,
        &format!("(fib {})", n),
    );
}

#[bench]
fn bench_compile_0(b: &mut Bencher) {
    b.iter(|| {
        let interp = Interpreter::new();

        interp
            .compile_single_expr(
                r#"
            (define (foo) ())
            "#,
                None,
            ).unwrap();
    });
}

#[bench]
fn bench_compile_1(b: &mut Bencher) {
    b.iter(|| {
        let interp = Interpreter::new();

        interp
            .compile_single_expr(
                r#"
            (define (foo a b)
              (if (< a b) a b))
            "#,
                None,
            ).unwrap();
    });
}

#[bench]
fn bench_compile_2(b: &mut Bencher) {
    b.iter(|| {
        let interp = Interpreter::new();

        interp
            .compile_single_expr(
                r#"
            (define (foo a b :optional (c 0) (d c))
              (if a
                b
                (case c
                  ((0 1 2 3)  (bar a b c d))
                  ((4 5 6 7)  (baz d c b a))
                  (else       (cond
                                ((= a 'a) 'alpha)
                                ((<= b 9) 'beta)
                                (else     'gamma))))))
            "#,
                None,
            ).unwrap();
    });
}

#[bench]
fn bench_fib_100(b: &mut Bencher) {
    fib(b, 100);
}

#[bench]
fn bench_factorial_100(b: &mut Bencher) {
    factorial(b, 100);
}
