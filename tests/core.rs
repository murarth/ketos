extern crate ketos;

use ketos::{CompileError, Error, ExecError, Interpreter, FromValue, Value};

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

fn eval(s: &str) -> Result<String, Error> {
    let interp = Interpreter::new();

    let v = try!(interp.run_single_expr(s, None));
    Ok(interp.format_value(&v))
}

fn eval_str(s: &str) -> Result<String, Error> {
    let interp = Interpreter::new();

    let v = try!(interp.run_single_expr(s, None));

    let s = FromValue::from_value(v).unwrap();
    Ok(s)
}

fn run(s: &str) -> Result<Vec<String>, Error> {
    let interp = Interpreter::new();

    let c = try!(interp.compile_exprs(s));
    c.into_iter().map(|c| interp.execute(c)
        .map(|v| interp.format_value(&v))).collect()
}

#[test]
fn test_integer() {
    assert_eq!(eval("123").unwrap(), "123");
    assert_eq!(eval("-123").unwrap(), "-123");
    assert_eq!(eval("0xfaff").unwrap(), "64255");
    assert_eq!(eval("0o777").unwrap(), "511");
    assert_eq!(eval("0b101101").unwrap(), "45");
}

#[test]
fn test_quasiquote() {
    assert_eq!(eval("`(foo ,(id 1))").unwrap(), "(foo 1)");
    assert_eq!(eval("``(foo ,(id ,(id 1)))").unwrap(), "`(foo ,(id 1))");
    assert_eq!(eval("```(foo ,(id ,(id ,(id 1))))").unwrap(),
        "``(foo ,(id ,(id 1)))");

    assert_eq!(eval("`(,@(list 1 2 3))").unwrap(), "(1 2 3)");
    assert_eq!(eval("`(foo ,@(list 1 2 3))").unwrap(), "(foo 1 2 3)");
    assert_eq!(eval("`(foo ,@(list 1 2 3) bar)").unwrap(),
        "(foo 1 2 3 bar)");
    assert_eq!(eval("`(foo ,@(list 1 2 3) bar ,@(list 4 5 6))").unwrap(),
        "(foo 1 2 3 bar 4 5 6)");
    assert_eq!(eval("`(foo ,@(list 1 2 3) bar ,@(list 4 5 6) baz)").unwrap(),
        "(foo 1 2 3 bar 4 5 6 baz)");
}

#[test]
fn test_struct() {
    assert_eq!(run("
        (struct foo ())
        (struct bar ())
        (define my-foo (new foo))
        (is-instance foo my-foo)
        (is-instance bar my-foo)
        ").unwrap(),
        ["foo", "bar", "my-foo", "true", "false"]);

    assert_eq!(run("
        (struct foo ((a integer)
                     (b list)
                     (c bool)))

        (define my-foo (new foo
                            :a 123
                            :b '(4 5 6)
                            :c true))

        (. my-foo :a)
        (. my-foo :b)
        (. my-foo :c)

        (define new-foo (.= my-foo
                            :a 456
                            :b '(7 8 9)
                            :c false))

        (. new-foo :a)
        (. new-foo :b)
        (. new-foo :c)
        ").unwrap(),
        ["foo",
            "my-foo", "123", "(4 5 6)", "true",
            "new-foo", "456", "(7 8 9)", "false"]);

    assert_eq!(run("
        (struct foo ((a number)))
        (new foo :a 1)
        (new foo :a 1.0)
        ").unwrap(), ["foo", "foo { a: 1 }", "foo { a: 1 }"]);

    assert_eq!(run("
        (struct foo ())
        (define my-foo (new foo))
        (is-instance foo my-foo)
        (struct foo ())
        (is-instance foo my-foo)
        ").unwrap(), ["foo", "my-foo", "true", "foo", "false"]);

    assert_matches!(run("
        (struct foo ((a integer)))
        (new foo)
        ").unwrap_err(),
        Error::ExecError(ExecError::MissingField{..}));

    assert_matches!(run("
        (struct foo ((a integer)))
        (new foo :a 1.0)
        ").unwrap_err(),
        Error::ExecError(ExecError::FieldTypeError{..}));

    assert_matches!(run("
        (struct foo ((a integer)))
        (.= (new foo :a 1) :a 1.0)
        ").unwrap_err(),
        Error::ExecError(ExecError::FieldTypeError{..}));

    assert_matches!(run("
        (struct foo ((a integer)))
        (. (new foo :a 1) :b)
        ").unwrap_err(),
        Error::ExecError(ExecError::FieldError{..}));

    assert_eq!(run("
        (struct foo ((a number)))
        (= (new foo :a 1) (new foo :a 1.0))
        ").unwrap(),
        ["foo", "true"]);
}

#[test]
fn test_format() {
    assert_eq!(eval_str(r#"(format "foo")"#).unwrap(), "foo");
    assert_eq!(eval_str(r#"(format "foo~a" "bar")"#).unwrap(), "foobar");
    assert_eq!(eval_str(r#"(format "foo~s" "bar")"#).unwrap(), "foo\"bar\"");

    assert_eq!(eval_str(r#"(format "~5a" "foo")"#).unwrap(), "foo  ");
    assert_eq!(eval_str(r#"(format "~5@a" "foo")"#).unwrap(), "  foo");
    assert_eq!(eval_str(r#"(format "~7s" "foo")"#).unwrap(), "\"foo\"  ");
    assert_eq!(eval_str(r#"(format "~7@s" "foo")"#).unwrap(), "  \"foo\"");

    assert_eq!(eval_str(r#"(format "~5,4a" "foo")"#).unwrap(), "foo    ");
    assert_eq!(eval_str(r#"(format "~5,4@a" "foo")"#).unwrap(), "    foo");

    assert_eq!(eval_str(r#"(format "~,,3,'-a" "foo")"#).unwrap(), "foo---");

    assert_eq!(eval_str(r#"(format "~a" 123)"#).unwrap(), "123");
    assert_eq!(eval_str(r#"(format "~s" 123)"#).unwrap(), "123");
    assert_eq!(eval_str(r#"(format "~s" 'foo)"#).unwrap(), "foo");
    assert_eq!(eval_str(r#"(format "~a" #'a')"#).unwrap(), "a");
    assert_eq!(eval_str(r#"(format "~s" #'a')"#).unwrap(), "#'a'");

    assert_eq!(eval_str(r#"(format "foo~c~c~c" #'b' #'a' #'r')"#).unwrap(), "foobar");

    assert_eq!(eval_str(r#"(format "~f" 1.0)"#).unwrap(), "1");
    assert_eq!(eval_str(r#"(format "~e" 1.0)"#).unwrap(), "1e0");
    assert_eq!(eval_str(r#"(format "~d" 123)"#).unwrap(), "123");

    assert_eq!(eval_str(r#"(format "~d" 1.2)"#).unwrap(), "1");
    assert_eq!(eval_str(r#"(format "~d" 11/10)"#).unwrap(), "1");
    assert_eq!(eval_str(r#"(format "~f" 1)"#).unwrap(), "1");
    assert_eq!(eval_str(r#"(format "~f" 1/2)"#).unwrap(), "0.5");

    assert_eq!(eval_str(r#"(format "~4f" 1.0)"#).unwrap(), "   1");
    assert_eq!(eval_str(r#"(format "~4f" -1.0)"#).unwrap(), "  -1");
    assert_eq!(eval_str(r#"(format "~,3f" 1.0)"#).unwrap(), "1.000");
    assert_eq!(eval_str(r#"(format "~4,,'*f" 1.0)"#).unwrap(), "***1");
    assert_eq!(eval_str(r#"(format "~4,,'*e" 1.0)"#).unwrap(), "*1e0");

    assert_eq!(eval_str(r#"(format "~@d" 0)"#).unwrap(), "+0");
    assert_eq!(eval_str(r#"(format "~@d" 1)"#).unwrap(), "+1");
    assert_eq!(eval_str(r#"(format "~@d" -1)"#).unwrap(), "-1");

    assert_eq!(eval_str(r#"(format "~5d" 123)"#).unwrap(), "  123");
    assert_eq!(eval_str(r#"(format "~:d" 1234567890)"#).unwrap(), "1,234,567,890");
    assert_eq!(eval_str(r#"(format "~:d" -123456)"#).unwrap(), "-123,456");
    assert_eq!(eval_str(r#"(format "~,,' ,2:d" 12345)"#).unwrap(), "1 23 45");

    assert_matches!(eval_str(r#"(format "~v,vd" 5 6 123)"#).unwrap_err(),
        Error::ExecError(ExecError::FormatError{..}));
    assert_eq!(eval_str(r#"(format "~v,vd" 5 #'*' 123)"#).unwrap(), "**123");
    assert_eq!(eval_str(r#"(format "~,,v,v:d" #'.' 2 123)"#).unwrap(), "1.23");
    assert_eq!(eval_str(r#"(format "~v,v,v,v:d" 5 #'*' #'.' 2 123)"#).unwrap(),
        "*1.23");

    assert_eq!(eval_str(r#"(format "~4@f" 1.0)"#).unwrap(), "  +1");
    assert_eq!(eval_str(r#"(format "~,3@f" 1.0)"#).unwrap(), "+1.000");
    assert_eq!(eval_str(r#"(format "~4,,'*@f" 1.0)"#).unwrap(), "**+1");

    assert_eq!(eval_str(r#"(format "~d thing~:p" 0)"#).unwrap(), "0 things");
    assert_eq!(eval_str(r#"(format "~d thing~:p" 1)"#).unwrap(), "1 thing");
    assert_eq!(eval_str(r#"(format "~d thing~:p" 2)"#).unwrap(), "2 things");

    assert_eq!(eval_str(r#"(format "~d thing~:@p" 0)"#).unwrap(), "0 thingies");
    assert_eq!(eval_str(r#"(format "~d thing~:@p" 1)"#).unwrap(), "1 thingy");
    assert_eq!(eval_str(r#"(format "~d thing~:@p" 2)"#).unwrap(), "2 thingies");

    assert_eq!(eval_str(r#"(format "~d thing~p" 1 2)"#).unwrap(), "1 things");

    assert_eq!(eval_str(r#"(format "~t")"#).unwrap(), " ");
    assert_eq!(eval_str(r#"(format "~4t")"#).unwrap(), "    ");
    assert_eq!(eval_str(r#"(format "ab~4t")"#).unwrap(), "ab  ");
    assert_eq!(eval_str(r#"(format "abc~4t")"#).unwrap(), "abc ");
    assert_eq!(eval_str(r#"(format "abcd~4t")"#).unwrap(), "abcd ");
    assert_eq!(eval_str(r#"(format "abcde~4,4t")"#).unwrap(), "abcde   ");
    assert_eq!(eval_str(r#"(format "abcdef~4,4t")"#).unwrap(), "abcdef  ");
    assert_eq!(eval_str(r#"(format "abcdefg~4,4t")"#).unwrap(), "abcdefg ");
    assert_eq!(eval_str(r#"(format "abcdefgh~4,4t")"#).unwrap(), "abcdefgh    ");
    assert_eq!(eval_str(r#"(format "ab~2,4@t")"#).unwrap(), "ab  ");
    assert_eq!(eval_str(r#"(format "abc~2,4@t")"#).unwrap(), "abc     ");

    assert_eq!(eval_str(r#"(format "~~")"#).unwrap(), "~");
    assert_eq!(eval_str(r#"(format "~3~")"#).unwrap(), "~~~");
    assert_eq!(eval_str(r#"(format "~v~" 5)"#).unwrap(), "~~~~~");
    assert_eq!(eval_str(r#"(format "~#~" 1 2)"#).unwrap(), "~~");
    assert_eq!(eval_str(r#"(format "~%")"#).unwrap(), "\n");
    assert_eq!(eval_str(r#"(format "foo~
                                    bar")"#).unwrap(), "foobar");
    assert_eq!(eval_str(r#"(format "~&")"#).unwrap(), "");
    assert_eq!(eval_str(r#"(format "a~&b")"#).unwrap(), "a\nb");
    assert_eq!(eval_str(r#"(format "a~%~&b")"#).unwrap(), "a\nb");
    assert_eq!(eval_str(r#"(format "~2&")"#).unwrap(), "\n");
    assert_eq!(eval_str(r#"(format "a~2&b")"#).unwrap(), "a\n\nb");
    assert_eq!(eval_str(r#"(format "a~%~2&b")"#).unwrap(), "a\n\nb");

    assert_eq!(eval_str(r#"(format "~a ~*~a" 0 1 2)"#).unwrap(), "0 2");
    assert_eq!(eval_str(r#"(format "~a ~:*~a" 0)"#).unwrap(), "0 0");
    assert_matches!(eval_str(r#"(format "~*~*~*~a" 0 1 2)"#).unwrap_err(),
        Error::ExecError(ExecError::FormatError{..}));
    assert_eq!(eval_str(r#"(format "~a ~@*~a" 0)"#).unwrap(), "0 0");
    assert_eq!(eval_str(r#"(format "~a ~2@*~a" 0 1 2)"#).unwrap(), "0 2");

    assert_eq!(eval_str(r#"(format "~?" "~a ~a" '(1 2))"#).unwrap(), "1 2");
    assert_eq!(eval_str(r#"(format "~@?" "~a ~a" 1 2)"#).unwrap(), "1 2");

    assert_eq!(eval_str(r#"(format "FOO~(BAR~)")"#).unwrap(), "FOObar");
    assert_eq!(eval_str(r#"(format "foo~:@(bar~)")"#).unwrap(), "fooBAR");
    assert_eq!(eval_str(r#"(format "foo ~@(bar baz~)")"#).unwrap(), "foo Bar baz");
    assert_eq!(eval_str(r#"(format "foo~@( bar baz~)")"#).unwrap(), "foo Bar baz");
    assert_eq!(eval_str(r#"(format "foo ~:(bar baz~)")"#).unwrap(), "foo Bar Baz");
    assert_eq!(eval_str(r#"(format "~(FOO~^BAR~)")"#).unwrap(), "foo");

    assert_eq!(eval_str(r#"(format "~[foo~;bar~;baz~]" 0)"#).unwrap(), "foo");
    assert_eq!(eval_str(r#"(format "~[foo~;bar~;baz~]" 1)"#).unwrap(), "bar");
    assert_eq!(eval_str(r#"(format "~[foo~;bar~;baz~]" 2)"#).unwrap(), "baz");
    assert_eq!(eval_str(r#"(format "~[foo~;bar~;baz~]" 3)"#).unwrap(), "");

    assert_eq!(eval_str(r#"(format "~[foo~;bar~:;baz~]" 3)"#).unwrap(), "baz");
    assert_eq!(eval_str(r#"(format "~[foo~;bar~:;baz~;quux~]" 3)"#).unwrap(), "baz");

    assert_eq!(eval_str(r#"(format "~:[foo~;bar~]" false)"#).unwrap(), "foo");
    assert_eq!(eval_str(r#"(format "~:[foo~;bar~]" true)"#).unwrap(), "bar");
    assert_matches!(eval_str(r#"(format "~:[foo~;bar~]" 'other)"#).unwrap_err(),
        Error::ExecError(ExecError::FormatError{..}));

    assert_eq!(eval_str(r#"(format "~@[~a~]" ())"#).unwrap(), "");
    assert_eq!(eval_str(r#"(format "~@[~a~]" "foo")"#).unwrap(), "foo");
    assert_eq!(eval_str(r#"(format "~@[~a~]" false)"#).unwrap(), "false");

    assert_eq!(eval_str(r#"(format "~{~a~}" '(1 2 3))"#).unwrap(), "123");
    assert_eq!(eval_str(r#"(format "~{~}" "~a" '(1 2 3))"#).unwrap(), "123");

    assert_eq!(eval_str(r#"(format "~{~{~a ~a~}~^, ~}" '((a b) (c d)))"#).unwrap(), "a b, c d");

    assert_eq!(eval_str(r#"(format "~{foo~^~a~:}" '())"#).unwrap(), "foo");
    assert_eq!(eval_str(r#"(format "~{foo~^~a~:}" '(1 2))"#).unwrap(), "foo1foo2");
    assert_eq!(eval_str(r#"(format "~0{foo~:}" '())"#).unwrap(), "");
    assert_eq!(eval_str(r#"(format "~2{~a~:}" '(1 2 3))"#).unwrap(), "12");
    assert_eq!(eval_str(r#"(format "~{foo~0^~:}" '(1 2 3))"#).unwrap(), "foo");
    assert_eq!(eval_str(r#"(format "~:{~@?~^:~}" '(("a") ("b")))"#).unwrap(), "ab");
    assert_eq!(eval_str(r#"(format "~:{~@?~:^:~}" '(("a") ("b")))"#).unwrap(), "a:b");

    assert_eq!(eval_str(r#"(format "~:{foo~a~0^bar~:}" '((1 2) (3 4)))"#).unwrap(),
        "foo1foo3");
    assert_eq!(eval_str(r#"(format "~:{foo~a~0:^bar~:}" '((1 2) (3 4)))"#).unwrap(),
        "foo1");

    assert_matches!(eval_str(r#"(format "~{infinite-loop~}" '(1 2 3))"#).unwrap_err(),
        Error::ExecError(ExecError::FormatError{..}));
    assert_matches!(eval_str(r#"(format "~@{infinite-loop~}" 1 2 3)"#).unwrap_err(),
        Error::ExecError(ExecError::FormatError{..}));

    assert_eq!(eval_str(r#"(format "~?baz" "foo~^bar" ())"#).unwrap(), "foobaz");

    assert_eq!(eval_str(r#"(format "foo~^bar")"#).unwrap(), "foo");
    assert_eq!(eval_str(r#"(format "~:@(foo~^bar~)baz")"#).unwrap(), "FOO");
    assert_eq!(eval_str(r#"(format "~[foo~^bar~;baz~]quux" 0)"#).unwrap(),
        "foo");
    assert_eq!(eval_str(r#"(format "~[foo~^bar~;baz~]quux" 1)"#).unwrap(),
        "bazquux");
    assert_eq!(eval_str(r#"(format "~[foo~^bar~;baz~]quux" 2)"#).unwrap(),
        "quux");

    assert_eq!(eval_str(r#"(format "~{foo ~a ~^bar ~}baz" '())"#).unwrap(),
        "baz");
    assert_eq!(eval_str(r#"(format "~{foo ~a ~^bar ~}baz" '(1))"#).unwrap(),
        "foo 1 baz");
    assert_eq!(eval_str(r#"(format "~{foo ~a ~^bar ~}baz" '(1 2))"#).unwrap(),
        "foo 1 bar foo 2 baz");

    assert_eq!(eval_str(r#"(format "~{a ~a~^ b ~a~^ ~}" '())"#).unwrap(),
        "");
    assert_eq!(eval_str(r#"(format "~{a ~a~^ b ~a~^ ~}" '(1))"#).unwrap(),
        "a 1");
    assert_eq!(eval_str(r#"(format "~{a ~a~^ b ~a~^ ~}" '(1 2))"#).unwrap(),
        "a 1 b 2");
    assert_eq!(eval_str(r#"(format "~{a ~a~^ b ~a~^ ~}" '(1 2 3))"#).unwrap(),
        "a 1 b 2 a 3");

    assert_eq!(eval_str(r#"(format "~<~>")"#).unwrap(), "");
    assert_eq!(eval_str(r#"(format "~<a~>")"#).unwrap(), "a");
    assert_eq!(eval_str(r#"(format "~5<a~>")"#).unwrap(), "    a");
    assert_eq!(eval_str(r#"(format "~5@<a~>")"#).unwrap(), "a    ");
    assert_eq!(eval_str(r#"(format "~5:<a~>")"#).unwrap(), "    a");
    assert_eq!(eval_str(r#"(format "~5:@<a~>")"#).unwrap(), "  a  ");

    assert_eq!(eval_str(r#"(format "~5<a~;b~;c~>")"#).unwrap(), "a b c");
    assert_eq!(eval_str(r#"(format "~6<a~;b~;c~>")"#).unwrap(), "a  b c");
    assert_eq!(eval_str(r#"(format "~7<a~;b~;c~>")"#).unwrap(), "a  b  c");

    assert_eq!(eval_str(r#"(format "~<foo:~,5:;aaaaa~>")"#).unwrap(), "aaaaa");
    assert_eq!(eval_str(r#"(format "~<foo:~,5:;aaaaaa~>")"#).unwrap(), "foo:aaaaaa");

    assert_matches!(eval_str(r#"(format "~(~]")"#).unwrap_err(),
        Error::ExecError(ExecError::FormatError{..}));
    assert_matches!(eval_str(r#"(format "~}")"#).unwrap_err(),
        Error::ExecError(ExecError::FormatError{..}));
}

#[test]
fn test_format_radix() {
    assert_matches!(eval_str(r#"(format "~@r" 0)"#).unwrap_err(),
        Error::ExecError(ExecError::FormatError{..}));
    assert_matches!(eval_str(r#"(format "~@:r" 0)"#).unwrap_err(),
        Error::ExecError(ExecError::FormatError{..}));

    assert_eq!(eval_str(r#"(format "~10r" 0)"#).unwrap(), "0");
    assert_eq!(eval_str(r#"(format "~10r" 123)"#).unwrap(), "123");
    assert_eq!(eval_str(r#"(format "~vr" 10 123)"#).unwrap(), "123");
    assert_eq!(eval_str(r#"(format "~10,5,'*r" 123)"#).unwrap(), "**123");

    assert_eq!(eval_str(r#"(format "~2r" 0b111000111000)"#).unwrap(), "111000111000");
    assert_eq!(eval_str(r#"(format "~8r" 0o777)"#).unwrap(), "777");
    assert_eq!(eval_str(r#"(format "~16r" 0xdeadbeef)"#).unwrap(), "deadbeef");
    assert_eq!(eval_str(r#"(format "~16r" (- 0xff))"#).unwrap(), "-ff");
    assert_eq!(eval_str(r#"(format "~36r"
        158401117505150402526146910133459374380313782878846610247207502179)"#)
        .unwrap(), "omghowdidthisgethereiamnotgoodwithcomputer");

    assert_eq!(eval_str(r#"(format "~b" 0b1010)"#).unwrap(), "1010");
    assert_eq!(eval_str(r#"(format "~o" 0o321)"#).unwrap(), "321");
    assert_eq!(eval_str(r#"(format "~x" 0xabcdef)"#).unwrap(), "abcdef");

    assert_eq!(eval_str(r#"(format "~2,,,' ,4:r" 0b101011001111)"#).unwrap(),
        "1010 1100 1111");

    assert_eq!(eval_str(r#"(format "~r" 0)"#).unwrap(), "zero");
    assert_eq!(eval_str(r#"(format "~r" 1)"#).unwrap(), "one");
    assert_eq!(eval_str(r#"(format "~r" 2)"#).unwrap(), "two");
    assert_eq!(eval_str(r#"(format "~r" 3)"#).unwrap(), "three");
    assert_eq!(eval_str(r#"(format "~r" 15)"#).unwrap(), "fifteen");
    assert_eq!(eval_str(r#"(format "~r" 41)"#).unwrap(), "forty-one");
    assert_eq!(eval_str(r#"(format "~r" 101)"#).unwrap(), "one hundred one");
    assert_eq!(eval_str(r#"(format "~r" 1204)"#).unwrap(), "one thousand two hundred four");

    assert_eq!(eval_str(r#"(format "~:r" 0)"#).unwrap(), "zeroth");
    assert_eq!(eval_str(r#"(format "~:r" 1)"#).unwrap(), "first");
    assert_eq!(eval_str(r#"(format "~:r" 2)"#).unwrap(), "second");
    assert_eq!(eval_str(r#"(format "~:r" 3)"#).unwrap(), "third");
    assert_eq!(eval_str(r#"(format "~:r" 15)"#).unwrap(), "fifteenth");
    assert_eq!(eval_str(r#"(format "~:r" 41)"#).unwrap(), "forty-first");
    assert_eq!(eval_str(r#"(format "~:r" 101)"#).unwrap(), "one hundred first");
    assert_eq!(eval_str(r#"(format "~:r" 1204)"#).unwrap(), "one thousand two hundred fourth");

    assert_eq!(eval_str(r#"(format "~@r" 1)"#).unwrap(), "I");
    assert_eq!(eval_str(r#"(format "~@r" 2)"#).unwrap(), "II");
    assert_eq!(eval_str(r#"(format "~@r" 3)"#).unwrap(), "III");
    assert_eq!(eval_str(r#"(format "~@r" 15)"#).unwrap(), "XV");
    assert_eq!(eval_str(r#"(format "~@r" 41)"#).unwrap(), "XLI");
    assert_eq!(eval_str(r#"(format "~@r" 101)"#).unwrap(), "CI");
    assert_eq!(eval_str(r#"(format "~@r" 1204)"#).unwrap(), "MCCIV");

    assert_eq!(eval_str(r#"(format "~@:r" 1)"#).unwrap(), "I");
    assert_eq!(eval_str(r#"(format "~@:r" 2)"#).unwrap(), "II");
    assert_eq!(eval_str(r#"(format "~@:r" 3)"#).unwrap(), "III");
    assert_eq!(eval_str(r#"(format "~@:r" 15)"#).unwrap(), "XV");
    assert_eq!(eval_str(r#"(format "~@:r" 41)"#).unwrap(), "XXXXI");
    assert_eq!(eval_str(r#"(format "~@:r" 101)"#).unwrap(), "CI");
    assert_eq!(eval_str(r#"(format "~@:r" 1204)"#).unwrap(), "MCCIIII");
}

#[test]
fn test_add() {
    assert_eq!(eval("(+)").unwrap(), "0");
    assert_eq!(eval("(+ 1 2)").unwrap(), "3");
    assert_eq!(eval("(+ 1 2 3 4)").unwrap(), "10");
    assert_eq!(eval("(+ (+ 1 2) (+ 3 4))").unwrap(), "10");

    assert_eq!(eval("(+ 1.0 2.0)").unwrap(), "3");
    assert_eq!(eval("(+ 1/3 1/2)").unwrap(), "5/6");

    assert_eq!(eval("(+ 1 1/2)").unwrap(), "3/2");
    assert_eq!(eval("(+ 1 0.5)").unwrap(), "1.5");
    assert_eq!(eval("(+ 1/4 0.5)").unwrap(), "0.75");
}

#[test]
fn test_sub() {
    assert_eq!(eval("(- 3 2)").unwrap(), "1");
    assert_eq!(eval("(- 5 4 3)").unwrap(), "-2");

    assert_eq!(eval("(- 1 3/4)").unwrap(), "1/4");
    assert_eq!(eval("(- 1.0 3/4)").unwrap(), "0.25");
}

#[test]
fn test_mul() {
    assert_eq!(eval("(*)").unwrap(), "1");
    assert_eq!(eval("(* 3 2)").unwrap(), "6");
    assert_eq!(eval("(* 100 200 0)").unwrap(), "0");

    assert_eq!(eval("(* 1/2 1/2)").unwrap(), "1/4");
    assert_eq!(eval("(* 0.5 1/2)").unwrap(), "0.25");

    assert_eq!(eval("(* 2 0.5)").unwrap(), "1");
    assert_eq!(eval("(* 2 1/2)").unwrap(), "1");

    assert_eq!(eval("(type-of (* 2 0.5))").unwrap(), "float");
    assert_eq!(eval("(type-of (* 2 1/2))").unwrap(), "ratio");
}

#[test]
fn test_pow() {
    assert_eq!(eval("(^ 2 10)").unwrap(), "1024");
    assert_eq!(eval("(^ 2 -1)").unwrap(), "0.5");
    assert_eq!(eval("(^ 2.0 -1.0)").unwrap(), "0.5");

    assert_eq!(eval("(^ 2/3 10)").unwrap(), "1024/59049");
    assert_eq!(eval("(^ 2/3 10/1)").unwrap(), "1024/59049");
    assert_eq!(eval("(^ 2/3 0)").unwrap(), "1");
    assert_eq!(eval("(^ 2/3 -1)").unwrap(), "1.5");

    assert_eq!(eval("(type-of (^ 2/3 10))").unwrap(), "ratio");
    assert_eq!(eval("(type-of (^ 2/3 10/1))").unwrap(), "ratio");
    assert_eq!(eval("(type-of (^ 2/3 0))").unwrap(), "ratio");
    assert_eq!(eval("(type-of (^ 2/3 1/2))").unwrap(), "float");
    assert_eq!(eval("(type-of (^ 2/3 -1))").unwrap(), "float");
}

#[test]
fn test_div() {
    assert_eq!(eval("(/ 10 2)").unwrap(), "5");
    assert_eq!(eval("(/ 12 2 2)").unwrap(), "3");

    assert_eq!(eval("(/ 5 2)").unwrap(), "5/2");
    assert_eq!(eval("(// 5 2)").unwrap(), "2");

    assert_eq!(eval("(/ 1.0 2.0)").unwrap(), "0.5");

    assert_eq!(eval("(/ 1/2 3/4)").unwrap(), "2/3");

    assert_eq!(eval("(/ 2 4)").unwrap(), "1/2");
    assert_eq!(eval("(/ 2 4.0)").unwrap(), "0.5");

    assert_matches!(eval("(/ 1 0)").unwrap_err(),
        Error::ExecError(ExecError::DivideByZero));
    assert_eq!(eval("(/ 1.0 0.0)").unwrap(), "inf");
    assert_matches!(eval("(/ 1/1 0/1)").unwrap_err(),
        Error::ExecError(ExecError::DivideByZero));
}

#[test]
fn test_rem() {
    assert_eq!(eval("(rem 10 3)").unwrap(), "1");

    assert_matches!(eval("(rem 1 0)").unwrap_err(),
        Error::ExecError(ExecError::DivideByZero));
    assert_eq!(eval("(rem 1.0 0.0)").unwrap(), "NaN");
    assert_matches!(eval("(rem 1/1 0/1)").unwrap_err(),
        Error::ExecError(ExecError::DivideByZero));
}

#[test]
fn test_shift() {
    assert_eq!(eval("(<< 1 10)").unwrap(), "1024");
    assert_eq!(eval("(>> 128 7)").unwrap(), "1");
    assert_matches!(eval("(<< 1 -1)").unwrap_err(),
        Error::ExecError(ExecError::Overflow));
    assert_matches!(eval("(<< 1 10000000000000)").unwrap_err(),
        Error::ExecError(ExecError::Overflow));
    assert_matches!(eval("(>> 1 -1)").unwrap_err(),
        Error::ExecError(ExecError::Overflow));
    assert_matches!(eval("(>> 1 10000000000000)").unwrap_err(),
        Error::ExecError(ExecError::Overflow));
}

#[test]
fn test_eq() {
    assert_eq!(eval("(= 1 1)").unwrap(), "true");
    assert_eq!(eval("(= 1 1 1 1)").unwrap(), "true");
    assert_eq!(eval("(= 1 2)").unwrap(), "false");
    assert_eq!(eval("(= 1 1 1 2)").unwrap(), "false");

    // Require optimal short-circuit behavior
    assert_eq!(eval("(= '(a 123) '(b ()))").unwrap(), "false");

    assert_eq!(eval("(= (nan) (nan))").unwrap(), "false");

    assert_eq!(eval(r#"(= "a" "a")"#).unwrap(), "true");
    assert_eq!(eval(r#"(= "a" "b")"#).unwrap(), "false");
    assert_eq!(eval(r"(= #'a' #'a')").unwrap(), "true");
    assert_eq!(eval(r"(= #'a' #'b')").unwrap(), "false");

    assert_eq!(eval("(= 'a 'a)").unwrap(), "true");
    assert_eq!(eval("(= 'a 'b)").unwrap(), "false");

    assert_eq!(eval("(= = =)").unwrap(), "true");
    assert_eq!(eval("(= id =)").unwrap(), "false");

    assert_eq!(run("
        (define (foo n) (+ n 1))
        (define (bar n) (+ n 1))

        (= foo foo)
        (= foo bar)
        ").unwrap(), ["foo", "bar", "true", "false"]);

    assert_eq!(eval("(= 1 1.0)").unwrap(), "true");
    assert_eq!(eval("(= 2 1.0)").unwrap(), "false");

    assert_eq!(eval("(= 1/1 1)").unwrap(), "true");
    assert_eq!(eval("(= 1/1 1.0)").unwrap(), "true");
}

#[test]
fn test_ne() {
    assert_eq!(eval("(/= 1 2 3 4)").unwrap(), "true");
    assert_eq!(eval("(/= 1 2 3 1)").unwrap(), "false");
    assert_eq!(eval("(/= 1 2 3 2)").unwrap(), "false");

    // Require optimal short-circuit behavior
    assert_eq!(eval("(/= '(a 123) '(b ()))").unwrap(), "true");

    assert_eq!(eval("(/= (nan) (nan))").unwrap(), "true");
}

#[test]
fn test_cmp() {
    assert_eq!(eval("(> 5 4 3 2 1)").unwrap(), "true");
    assert_eq!(eval("(> 5 4 3 2 3)").unwrap(), "false");
    assert_eq!(eval("(< 1 2 3 4 5)").unwrap(), "true");
    assert_eq!(eval("(<= 1 1 2 2 3)").unwrap(), "true");

    assert_eq!(eval("(< 1 1.5)").unwrap(), "true");
    assert_eq!(eval("(< 1/2 1)").unwrap(), "true");

    assert_eq!(eval("(< #'a' #'b')").unwrap(), "true");
    assert_eq!(eval(r#"(< "a" "b")"#).unwrap(), "true");

    assert_eq!(eval("(< () '(0))").unwrap(), "true");
    assert_eq!(eval("(> '(0) ())").unwrap(), "true");

    assert_matches!(eval("(< < <)").unwrap_err(),
        Error::ExecError(ExecError::CannotCompare("function")));

    assert_matches!(eval("(< 1.0 (nan))").unwrap_err(),
        Error::ExecError(ExecError::CompareNaN));
}

#[test]
fn test_zero() {
    assert_eq!(eval("(zero 0 0 0)").unwrap(), "true");
    assert_eq!(eval("(zero 0 1 0)").unwrap(), "false");
    assert_eq!(eval("(zero 0 0.0 0/1)").unwrap(), "true");

    assert_matches!(eval("(zero ())").unwrap_err(), Error::ExecError(
        ExecError::TypeError{
            expected: "number",
            found: "unit",
        }));
}

#[test]
fn test_min_max() {
    assert_eq!(eval("(max 1 2 3 2 1)").unwrap(), "3");
    assert_eq!(eval("(min 3 2 1 2 3)").unwrap(), "1");
}

#[test]
fn test_and() {
    assert_eq!(eval("(and true true)").unwrap(), "true");
    assert_eq!(eval("(and true false)").unwrap(), "false");
    assert_eq!(eval("(and false true)").unwrap(), "false");
    assert_eq!(eval("(and false (panic))").unwrap(), "false");

    assert_matches!(eval("(and () true)").unwrap_err(), Error::ExecError(
        ExecError::TypeError{
            expected: "bool",
            found: "unit",
        }));
}

#[test]
fn test_or() {
    assert_eq!(eval("(or false false)").unwrap(), "false");
    assert_eq!(eval("(or true false)").unwrap(), "true");
    assert_eq!(eval("(or false true)").unwrap(), "true");
    assert_eq!(eval("(or true (panic))").unwrap(), "true");

    assert_matches!(eval("(or () true)").unwrap_err(), Error::ExecError(
        ExecError::TypeError{
            expected: "bool",
            found: "unit",
        }));
}

#[test]
fn test_xor() {
    assert_eq!(eval("(xor true true)").unwrap(), "false");
    assert_eq!(eval("(xor false true)").unwrap(), "true");
    assert_eq!(eval("(xor true false)").unwrap(), "true");
    assert_eq!(eval("(xor false false)").unwrap(), "false");

    assert_matches!(eval("(xor () ())").unwrap_err(), Error::ExecError(
        ExecError::TypeError{
            expected: "bool",
            found: "unit",
        }));
}

#[test]
fn test_not() {
    assert_eq!(eval("(not true)").unwrap(), "false");
    assert_eq!(eval("(not false)").unwrap(), "true");

    assert_matches!(eval("(not ())").unwrap_err(), Error::ExecError(
        ExecError::TypeError{
            expected: "bool",
            found: "unit",
        }));
}

#[test]
fn test_if() {
    assert_eq!(eval("(if true 1 (panic))").unwrap(), "1");
    assert_eq!(eval("(if false (panic) 1)").unwrap(), "1");

    assert_matches!(eval("(if 0 () ())").unwrap_err(), Error::ExecError(
        ExecError::TypeError{
            expected: "bool",
            found: "integer",
        }));
}

#[test]
fn test_case() {
    assert_eq!(eval("(case 1
                           ((0) 'a))").unwrap(), "()");

    assert_eq!(eval("(case 1
                           ((0 1 2) 'a))").unwrap(), "a");

    assert_eq!(eval("(case 1
                           ((0)  'a)
                           (else 'b))").unwrap(), "b");

    assert_eq!(eval("(case 2
                           ((0) 'a)
                           ((1) 'b)
                           ((2) 'c))").unwrap(), "c");

    assert_matches!(eval("(case 0
                                ((0) 'a)
                                (else 'b)
                                ((1) 'c))").unwrap_err(),
        Error::CompileError(_));
}

#[test]
fn test_cond() {
    assert_eq!(eval("(cond (false 'a)
                           (true 'b))").unwrap(), "b");

    assert_eq!(eval("(cond (true 'a)
                           (true 'b))").unwrap(), "a");

    assert_eq!(eval("(cond (false 'a)
                           (false 'b))").unwrap(), "()");

    assert_eq!(eval("(cond (false 'a)
                           (false 'b)
                           (else 'c))").unwrap(), "c");

    assert_matches!(eval("(cond (false 'a)
                            (else 'b)
                            (true 'c))").unwrap_err(),
        Error::CompileError(_));
}

#[test]
fn test_let() {
    assert_eq!(eval("
        (let ((a 1)
              (b 2))
          (+ a b))
        ").unwrap(), "3");

    // Standard names CAN be overriden with let
    assert_eq!(eval("(let ((id 0)) id)").unwrap(), "0");
}

#[test]
fn test_chars() {
    assert_eq!(eval(r#"(chars "")"#).unwrap(), "()");
    assert_eq!(eval(r#"(chars "foo")"#).unwrap(), "(#'f' #'o' #'o')");
    assert_eq!(eval(r#"(chars "halo thar")"#).unwrap(),
        "(#'h' #'a' #'l' #'o' #' ' #'t' #'h' #'a' #'r')");
}

#[test]
fn test_string() {
    assert_eq!(eval(r#"(string #'a')"#).unwrap(), r#""a""#);
    assert_eq!(eval(r#"(string "foo")"#).unwrap(), r#""foo""#);
}

#[test]
fn test_slice() {
    assert_eq!(eval("(slice () 0 0)").unwrap(), "()");
    assert_matches!(eval("(slice () 0 1)").unwrap_err(),
        Error::ExecError(ExecError::OutOfBounds(1)));

    assert_eq!(eval("(slice '(1 2 3) 0 2)").unwrap(), "(1 2)");
    assert_eq!(eval("(slice '(1 2 3) 1 3)").unwrap(), "(2 3)");

    assert_eq!(eval(r#"(slice "" 0 0)"#).unwrap(), r#""""#);
    assert_eq!(eval(r#"(slice "foobar" 3 6)"#).unwrap(), r#""bar""#);
    assert_matches!(eval(r#"(slice "a\u{2022}" 1 2)"#).unwrap_err(),
        Error::ExecError(ExecError::NotCharBoundary(2)));
}

#[test]
fn test_append() {
    assert_eq!(eval("(append () 1 2)").unwrap(), "(1 2)");
    assert_eq!(eval("(append '(1 2) 3 4)").unwrap(), "(1 2 3 4)");
}

#[test]
fn test_elt() {
    assert_eq!(eval("(elt '(1 2) 0)").unwrap(), "1");
    assert_matches!(eval("(elt '(1 2) 2)").unwrap_err(),
        Error::ExecError(ExecError::OutOfBounds(2)));
    assert_matches!(eval("(elt () -1)").unwrap_err(),
        Error::ExecError(ExecError::Overflow));
}

#[test]
fn test_concat() {
    assert_eq!(eval("(concat '(1 2) () '(3 4))").unwrap(), "(1 2 3 4)");
    assert_eq!(eval(r#"(concat "foo" "" "bar")"#).unwrap(), r#""foobar""#);
    assert_eq!(eval(r#"(concat #'a' #'b')"#).unwrap(), r#""ab""#);
    assert_eq!(eval(r#"(concat "foo" #'b' #'a' #'r')"#).unwrap(), r#""foobar""#);
}

#[test]
fn test_join() {
    assert_eq!(eval("(join '(0) '(1 2) () '(3 4))").unwrap(), "(1 2 0 0 3 4)");
    assert_eq!(eval("(join '(0))").unwrap(), "()");
    assert_eq!(eval(r#"(join ":")"#).unwrap(), r#""""#);
    assert_eq!(eval(r#"(join ":" "foo" "" "bar")"#).unwrap(), r#""foo::bar""#);
    assert_eq!(eval(r#"(join #':' "foo" "" "bar")"#).unwrap(), r#""foo::bar""#);
    assert_eq!(eval(r#"(join #':' #'a' #'b')"#).unwrap(), r#""a:b""#);
    assert_eq!(eval(r#"(join ":" "foo" #'a' #'b' "bar")"#).unwrap(),
        r#""foo:a:b:bar""#);
}

#[test]
fn test_len() {
    assert_eq!(eval("(len ())").unwrap(), "0");
    assert_eq!(eval("(len '(1 2 3))").unwrap(), "3");

    assert_eq!(eval(r#"(len "")"#).unwrap(), "0");
    assert_eq!(eval(r#"(len "foo")"#).unwrap(), "3");

    assert_matches!(eval("(len 123)").unwrap_err(),
        Error::ExecError(ExecError::TypeError{..}));
}

#[test]
fn test_first_second() {
    assert_eq!(eval("(first '(1 2))").unwrap(), "1");
    assert_eq!(eval("(second '(1 2))").unwrap(), "2");
    assert_matches!(eval("(first ())").unwrap_err(),
        Error::ExecError(_));
    assert_matches!(eval("(second '(1))").unwrap_err(),
        Error::ExecError(ExecError::OutOfBounds(1)));
}

#[test]
fn test_list_fns() {
    assert_eq!(eval("(last '(1 2 3))").unwrap(), "3");
    assert_eq!(eval("(init '(1 2 3))").unwrap(), "(1 2)");
    assert_eq!(eval("(tail '(1 2 3))").unwrap(), "(2 3)");
    assert_eq!(eval("(init '(1))").unwrap(), "()");
    assert_eq!(eval("(tail '(1))").unwrap(), "()");
}

#[test]
fn test_list() {
    assert_eq!(eval("(list 1 2 (+ 1 2))").unwrap(), "(1 2 3)");
}

#[test]
fn test_reverse() {
    assert_eq!(eval("(reverse ())").unwrap(), "()");
    assert_eq!(eval("(reverse '(1 2 3))").unwrap(), "(3 2 1)");
}

/* TODO: These are commented out until standard library stuff is figured out.
 * Mainly, whether a standard library will exist and where the interpreter
 * will look for it by default.
 * With embedding being a main goal of `ketos`, it would be rather cumbersome
 * to require source files to be stashed in some mysterious location.
 * A build script could load the contents of source files at compile time
 * and put these into the interpreter to be read. However, that is an unusual
 * behavior for a language interpreter.
 * Perhaps, this should be an optional build feature so that standard library
 * development may be facilitated by loading source files from the filesystem
 * at runtime, in the traditional fashion.

#[test]
fn test_all() {
    assert_eq!(eval("(all (lambda (n) (> n 3)) '(3 4 5))").unwrap(), "false");
    assert_eq!(eval("(all (lambda (n) (> n 3)) '(4 5 6))").unwrap(), "true");
    assert_eq!(eval("(all (lambda (n) (> n 3)) '(3 4 'a))").unwrap(), "false");
}

#[test]
fn test_any() {
    assert_eq!(eval("(any (lambda (n) (> n 3)) '(0 1 2))").unwrap(), "false");
    assert_eq!(eval("(any (lambda (n) (> n 3)) '(3 4 5))").unwrap(), "true");
    assert_eq!(eval("(any (lambda (n) (> n 3)) '(4 5 6))").unwrap(), "true");
    assert_eq!(eval("(any (lambda (n) (> n 3)) '(3 4 'a))").unwrap(), "true");
}

#[test]
fn test_each() {
    assert_eq!(run("
        (define counter 0)
        (each (lambda (n) (define counter (+ counter n))) '(1 2 3))
        counter
        ").unwrap(),
        ["counter", "()", "6"]);
}

#[test]
fn test_fold() {
    assert_eq!(eval("(foldl + 0 '(1 2 3))").unwrap(), "6");
    assert_eq!(eval("(foldr (lambda (a b) (append b a))
                       () '(1 2 3))").unwrap(), "(3 2 1)");

    assert_eq!(eval("(foldl + 0 ())").unwrap(), "0");
    assert_eq!(eval("(foldr + 0 ())").unwrap(), "0");
}

#[test]
fn test_find() {
    assert_eq!(eval("(find zero '(1 2 3 0))").unwrap(), "0");
    assert_eq!(eval("(index zero '(1 2 3 0))").unwrap(), "3");
}

#[test]
fn test_filter() {
    assert_eq!(eval("(filter (lambda (elt) (not (zero elt)))
                             '(0 1 2 0 3 0))").unwrap(), "(1 2 3)");

    assert_eq!(eval("(count (lambda (elt) (>= elt 3))
                            '(1 2 3 4 5))").unwrap(), "3");
}

#[test]
fn test_map() {
    assert_eq!(eval("(map (lambda (n) (* n 2)) '(1 2 3))").unwrap(), "(2 4 6)");
}
*/

#[test]
fn test_abs() {
    assert_eq!(eval("(abs -1)").unwrap(), "1");
    assert_eq!(eval("(abs -1/2)").unwrap(), "1/2");
    assert_eq!(eval("(abs -1.5)").unwrap(), "1.5");
    assert_eq!(eval("(abs (- (inf)))").unwrap(), "inf");
}

#[test]
fn test_ceil() {
    assert_eq!(eval("(ceil 1)").unwrap(), "1");
    assert_eq!(eval("(ceil 1/2)").unwrap(), "1");
    assert_eq!(eval("(ceil 1.3)").unwrap(), "2");
}

#[test]
fn test_floor() {
    assert_eq!(eval("(floor 1)").unwrap(), "1");
    assert_eq!(eval("(floor 1/2)").unwrap(), "0");
    assert_eq!(eval("(floor -1.3)").unwrap(), "-2");
}

#[test]
fn test_trunc() {
    assert_eq!(eval("(trunc 1)").unwrap(), "1");
    assert_eq!(eval("(trunc -1.3)").unwrap(), "-1");
    assert_eq!(eval("(trunc 5/2)").unwrap(), "2");
}

#[test]
fn test_int() {
    assert_eq!(eval("(int 123)").unwrap(), "123");
    assert_eq!(eval("(int 123.0)").unwrap(), "123");
    assert_eq!(eval("(int 123/1)").unwrap(), "123");
    assert_matches!(eval("(int (inf))").unwrap_err(),
        Error::ExecError(ExecError::Overflow));
    assert_matches!(eval("(int (nan))").unwrap_err(),
        Error::ExecError(ExecError::Overflow));
    assert_eq!(eval("(type-of (int 123.45))").unwrap(), "integer");
    assert_eq!(eval("(type-of (int 123/1))").unwrap(), "integer");
}

#[test]
fn test_float() {
    assert_eq!(eval("(float 123)").unwrap(), "123");
    assert_eq!(eval("(float 123.0)").unwrap(), "123");
    assert_eq!(eval("(float 123/1)").unwrap(), "123");
    assert_eq!(eval("(type-of (float 123))").unwrap(), "float");
    assert_eq!(eval("(type-of (float 123/1))").unwrap(), "float");
}

#[test]
fn test_inf() {
    assert_eq!(eval("(inf)").unwrap(), "inf");
    assert_eq!(eval("(- (inf))").unwrap(), "-inf");
    assert_eq!(eval("(inf (inf) (inf))").unwrap(), "true");
    assert_eq!(eval("(inf (- (inf)))").unwrap(), "true");
    assert_eq!(eval("(inf (inf) 1.0)").unwrap(), "false");
}

#[test]
fn test_nan() {
    assert_eq!(eval("(nan)").unwrap(), "NaN");
    assert_eq!(eval("(nan (nan) (nan))").unwrap(), "true");
    assert_eq!(eval("(nan (nan) 1.0)").unwrap(), "false");
}

#[test]
fn test_fract() {
    assert_eq!(eval("(fract 1.5)").unwrap(), "0.5");
    assert_eq!(eval("(fract 5/2)").unwrap(), "1/2");
}

#[test]
fn test_recip() {
    assert_eq!(eval("(recip 3)").unwrap(), "1/3");
    assert_eq!(eval("(recip 10.0)").unwrap(), "0.1");
    assert_eq!(eval("(recip 2/3)").unwrap(), "3/2");

    assert_matches!(eval("(recip 0)").unwrap_err(),
        Error::ExecError(ExecError::DivideByZero));
    assert_matches!(eval("(recip 0/1)").unwrap_err(),
        Error::ExecError(ExecError::DivideByZero));
}

#[test]
fn test_ratio() {
    assert_eq!(eval("(denom 1/2)").unwrap(), "2");
    assert_eq!(eval("(numer 1/2)").unwrap(), "1");

    assert_eq!(eval("(denom 123)").unwrap(), "1");
    assert_eq!(eval("(numer 123)").unwrap(), "123");

    assert_eq!(eval("(rat 1.5)").unwrap(), "3/2");
    assert_eq!(eval("(rat 1/3)").unwrap(), "1/3");
    assert_eq!(eval("(rat 3)").unwrap(), "3");
    assert_eq!(eval("(rat 1 2)").unwrap(), "1/2");
    assert_matches!(eval("(rat (inf))").unwrap_err(),
        Error::ExecError(ExecError::Overflow));
    assert_matches!(eval("(rat (nan))").unwrap_err(),
        Error::ExecError(ExecError::Overflow));
}

#[test]
fn test_id() {
    assert_eq!(eval("(id 1)").unwrap(), "1");
    assert_eq!(eval("(id #'a')").unwrap(), "#'a'");
    assert_eq!(eval("(id \"a\")").unwrap(), "\"a\"");
    assert_eq!(eval("(id '(1 2 3))").unwrap(), "(1 2 3)");
}

#[test]
fn test_is() {
    assert_eq!(eval("(is 'integer 1)").unwrap(), "true");
    assert_eq!(eval("(is 'ratio 1/1)").unwrap(), "true");
    assert_eq!(eval("(is 'float 1.0)").unwrap(), "true");
    assert_eq!(eval("(is 'list '(1))").unwrap(), "true");
    assert_eq!(eval("(is 'list ())").unwrap(), "true");
    assert_eq!(eval("(is 'unit ())").unwrap(), "true");
    assert_eq!(eval("(is 'name 'a)").unwrap(), "true");
    assert_eq!(eval("(is 'keyword :a)").unwrap(), "true");
    assert_eq!(eval("(is 'function is)").unwrap(), "true");
    assert_eq!(eval("(is 'lambda (lambda () ()))").unwrap(), "true");

    assert_eq!(eval("(is 'number 1)").unwrap(), "true");
    assert_eq!(eval("(is 'number 1/1)").unwrap(), "true");
    assert_eq!(eval("(is 'number 1.0)").unwrap(), "true");

    assert_eq!(eval("(is 'integer 1.0)").unwrap(), "false");
    assert_eq!(eval("(is 'list 'foo)").unwrap(), "false");
    assert_eq!(eval("(is 'foo ())").unwrap(), "false");
}

#[test]
fn test_null() {
    assert_eq!(eval("(null ())").unwrap(), "true");
    assert_eq!(eval("(null 'a)").unwrap(), "false");
    assert_eq!(eval("(null 1)").unwrap(), "false");
}

#[test]
fn test_type_of() {
    assert_eq!(eval("(type-of ())").unwrap(), "unit");
    assert_eq!(eval("(type-of true)").unwrap(), "bool");
    assert_eq!(eval("(type-of 1)").unwrap(), "integer");
    assert_eq!(eval("(type-of 1/1)").unwrap(), "ratio");
    assert_eq!(eval("(type-of 1.0)").unwrap(), "float");
    assert_eq!(eval("(type-of 'a)").unwrap(), "name");
    assert_eq!(eval("(type-of :a)").unwrap(), "keyword");
    assert_eq!(eval("(type-of #'a')").unwrap(), "char");
    assert_eq!(eval("(type-of \"a\")").unwrap(), "string");
    assert_eq!(eval("(type-of ''a)").unwrap(), "object");
    assert_eq!(eval("(type-of '(1))").unwrap(), "list");
    assert_eq!(eval("(type-of id)").unwrap(), "function");
    assert_eq!(eval("(type-of (lambda () ()))").unwrap(), "lambda");
}

#[test]
fn test_define() {
    assert_eq!(run("(define foo 123) foo").unwrap(),
        ["foo", "123"]);

    // Standard names cannot be overriden in global scope
    assert_matches!(run("(define (=) ())").unwrap_err(),
        Error::CompileError(_));
    assert_matches!(run("(define (if) ())").unwrap_err(),
        Error::CompileError(_));

    assert_eq!(run("(define (foo n) (* n n)) (foo 3)").unwrap(),
        ["foo", "9"]);
    assert_eq!(run("
        (define (foo a b :optional c d) (list a b c d))
        (foo 1 2)
        (foo 1 2 3)
        (foo 1 2 3 4)
        ").unwrap(),
        ["foo", "(1 2 () ())", "(1 2 3 ())", "(1 2 3 4)"]);

    assert_eq!(run("
        (define (foo a b :key c d) (list a b c d))
        (foo 1 2)
        (foo 1 2 :c 3)
        (foo 1 2 :d 3)
        (foo 1 2 :c 3 :d 4)
        ").unwrap(),
        ["foo", "(1 2 () ())", "(1 2 3 ())", "(1 2 () 3)", "(1 2 3 4)"]);

    assert_eq!(run("
        (define (foo a b :key (c 10) d) (list a b c d))
        (foo 1 2)
        (foo 1 2 :c 3)
        (foo 1 2 :d 3)
        (foo 1 2 :c 3 :d 4)
        ").unwrap(),
        ["foo", "(1 2 10 ())", "(1 2 3 ())", "(1 2 10 3)", "(1 2 3 4)"]);

    assert_eq!(run("
        (define (foo a b :key c (d 10)) (list a b c d))
        (foo 1 2)
        (foo 1 2 :c 3)
        (foo 1 2 :d 3)
        (foo 1 2 :c 3 :d 4)
        ").unwrap(),
        ["foo", "(1 2 () 10)", "(1 2 3 10)", "(1 2 () 3)", "(1 2 3 4)"]);

    assert_eq!(run("
        (define (foo a b :rest rest) (list a b rest))
        (foo 1 2)
        (foo 1 2 3)
        (foo 1 2 3 4)
        ").unwrap(),
        ["foo", "(1 2 ())", "(1 2 (3))", "(1 2 (3 4))"]);

    assert_eq!(run("
        (define (foo a b :optional c d :rest rest) (list a b c d rest))
        (foo 1 2)
        (foo 1 2 3)
        (foo 1 2 3 4)
        (foo 1 2 3 4 5)
        (foo 1 2 3 4 5 6)
        ").unwrap(),
        ["foo", "(1 2 () () ())", "(1 2 3 () ())", "(1 2 3 4 ())",
            "(1 2 3 4 (5))", "(1 2 3 4 (5 6))"]);

    assert_eq!(run("
        (define (foo a b :optional (c 10) d) (list a b c d))
        (foo 1 2)
        (foo 1 2 3)
        (foo 1 2 3 4)
        ").unwrap(),
        ["foo", "(1 2 10 ())", "(1 2 3 ())", "(1 2 3 4)"]);

    assert_eq!(run("
        (define (foo a b :optional c (d 10)) (list a b c d))
        (foo 1 2)
        (foo 1 2 3)
        (foo 1 2 3 4)
        ").unwrap(),
        ["foo", "(1 2 () 10)", "(1 2 3 10)", "(1 2 3 4)"]);

    assert_eq!(run("
        (define (foo a b :optional (c 10) (d 20) :rest rest) (list a b c d rest))
        (foo 1 2)
        (foo 1 2 3)
        (foo 1 2 3 4)
        (foo 1 2 3 4 5)
        (foo 1 2 3 4 5 6)
        ").unwrap(),
        ["foo", "(1 2 10 20 ())", "(1 2 3 20 ())", "(1 2 3 4 ())",
            "(1 2 3 4 (5))", "(1 2 3 4 (5 6))"]);

    assert_matches!(run("
        (define (foo a :optional b :key c) ())
        ").unwrap_err(),
        Error::CompileError(CompileError::SyntaxError(_)));

    assert_matches!(run("
        (define (foo a :key b :optional c) ())
        ").unwrap_err(),
        Error::CompileError(CompileError::SyntaxError(_)));

    assert_matches!(run("
        (define (foo a :key b :rest rest) ())
        ").unwrap_err(),
        Error::CompileError(CompileError::SyntaxError(_)));
}

#[test]
fn test_lambda() {
    assert_eq!(eval("((lambda (n) n) 1)").unwrap(), "1");
    assert_eq!(eval("((lambda (:rest rest) rest) 1 2 3)").unwrap(), "(1 2 3)");
}

#[test]
fn test_do() {
    assert_eq!(eval("(do 1 2 3)").unwrap(), "3");
}

#[test]
fn test_macro() {
    assert_eq!(run("
        (macro (quote a) `',a)
        (quote foo)
        ").unwrap(),
        ["quote", "foo"]);

    assert_matches!(eval("(define (foo a) (macro (bar) a))").unwrap_err(),
        Error::CompileError(_));

    assert_matches!(run("
        (macro (foo) '(bar))
        (macro (bar) '(foo))
        (foo)
        ").unwrap_err(),
        Error::CompileError(CompileError::MacroRecursionExceeded));
}

#[test]
fn test_apply() {
    assert_eq!(eval("(apply + '(1 2 3))").unwrap(), "6");
    assert_eq!(eval("(apply + 1 2 3 '(4 5 6))").unwrap(), "21");
}

#[test]
fn test_panic() {
    assert_matches!(eval("(panic)").unwrap_err(),
        Error::ExecError(ExecError::Panic(None)));
    assert_matches!(eval("(panic 123)").unwrap_err(),
        Error::ExecError(ExecError::Panic(Some(Value::Integer(ref i))))
            if i.to_u32() == Some(123));
    assert_matches!(eval("(panic \"foo\")").unwrap_err(),
        Error::ExecError(ExecError::Panic(Some(Value::String(ref s))))
            if s == "foo");
}

#[test]
fn test_use() {
    assert_eq!(run("
        (use math (sqrt))
        (sqrt 4.0)
        ").unwrap(),
        ["()", "2"]);

    assert_eq!(run("
        (use math :all)
        (sqrt 4.0)
        ").unwrap(),
        ["()", "2"]);
}
