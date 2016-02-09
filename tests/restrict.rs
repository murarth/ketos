#[macro_use] extern crate assert_matches;
extern crate ketos;

use std::time::Duration;

use ketos::{
    Builder,
    Error,
    RestrictConfig,
    RestrictError,
};

fn run(restrict: RestrictConfig, code: &str) -> Result<(), Error> {
    let interp = Builder::new()
        .restrict(restrict)
        .finish();

    try!(interp.run_code(code, None));
    Ok(())
}

macro_rules! assert_matches_re {
    ( $e:expr , $re:expr ) => {
        assert_matches!($e, Error::RestrictError(e) if e == $re)
    }
}

#[test]
fn test_restrict_time() {
    assert_matches_re!(run(
        RestrictConfig{
            execution_time: Some(Duration::from_millis(100)),
            .. RestrictConfig::permissive()
        },
        "
        (define (foo) (foo))
        (foo)
        ").unwrap_err(),
        RestrictError::ExecutionTimeExceeded);
}

#[test]
fn test_restrict_stack() {
    assert_matches_re!(run(
        RestrictConfig{
            call_stack_size: 100,
            .. RestrictConfig::permissive()
        },
        "
        (define (foo) (bar))
        (define (bar) (foo))
        (foo)
        ").unwrap_err(),
        RestrictError::CallStackExceeded);

    assert_matches_re!(run(
        RestrictConfig{
            value_stack_size: 100,
            .. RestrictConfig::permissive()
        },
        "
        (define (foo)
          (let ((a ()) (a ()) (a ()) (a ()) (a ()) (a ()) (a ()) (a ())
                (a ()) (a ()) (a ()) (a ()) (a ()) (a ()) (a ()) (a ())
                (a ()) (a ()) (a ()) (a ()) (a ()) (a ()) (a ()) (a ())
                (a ()) (a ()) (a ()) (a ()) (a ()) (a ()) (a ()) (a ()))
            (bar)))
        (define (bar) (foo))
        (foo)
        ").unwrap_err(),
        RestrictError::ValueStackExceeded);
}

#[test]
fn test_restrict_namespace() {
    { // This block is just so text editors can hide this nonsense.
        assert_matches_re!(run(
            RestrictConfig{
                namespace_size: 20,
                .. RestrictConfig::permissive()
            },
            "
            (define a-1 ())
            (define a-2 ())
            (define a-3 ())
            (define a-4 ())
            (define a-5 ())
            (define a-6 ())
            (define a-7 ())
            (define a-8 ())
            (define a-9 ())
            (define a-10 ())
            (define a-11 ())
            (define a-12 ())
            (define a-13 ())
            (define a-14 ())
            (define a-15 ())
            (define a-16 ())
            (define a-17 ())
            (define a-18 ())
            (define a-19 ())
            (define a-20 ())
            (define a-21 ())
            ").unwrap_err(),
            RestrictError::NamespaceSizeExceeded);
    }
}

#[test]
fn test_restrict_memory() {
    assert_matches_re!(run(
        RestrictConfig{
            memory_limit: 100,
            .. RestrictConfig::permissive()
        },
        "
        (define (foo a) (foo (list () a)))
        (foo ())
        ").unwrap_err(),
        RestrictError::MemoryLimitExceeded);
}

#[test]
fn test_restrict_integer() {
    let cfg = RestrictConfig{
        max_integer_size: 100,
        .. RestrictConfig::permissive()
    };

    assert_matches_re!(run(cfg.clone(), "
        0x10000000000000000000000000
        ").unwrap_err(),
        RestrictError::IntegerLimitExceeded);

    assert_matches_re!(run(cfg.clone(), "
        (^ 2 1_000_000)
        ").unwrap_err(),
        RestrictError::IntegerLimitExceeded);

    assert_matches_re!(run(cfg.clone(), "
        (<< 1 1_000_000)
        ").unwrap_err(),
        RestrictError::IntegerLimitExceeded);

    assert_matches_re!(run(cfg.clone(), "
        (define (foo n) (foo (* n 2)))
        (foo 1)
        ").unwrap_err(),
        RestrictError::IntegerLimitExceeded);

    assert_matches_re!(run(cfg.clone(), "
        (define (foo n) (foo (/ n 2)))
        (foo 1)
        ").unwrap_err(),
        RestrictError::IntegerLimitExceeded);
}

#[test]
fn test_restrict_syntax() {
    assert_matches_re!(run(
        RestrictConfig{
            max_syntax_nesting: 50,
            .. RestrictConfig::permissive()
        },
        "
        ((((((((((((((((((((((((((((((((((((((((((((((((((
        ((((((((((((((((((((((((((((((((((((((((((((((((((
        ))))))))))))))))))))))))))))))))))))))))))))))))))
        ))))))))))))))))))))))))))))))))))))))))))))))))))
        ").unwrap_err(),
        RestrictError::MaxSyntaxNestingExceeded);
}
