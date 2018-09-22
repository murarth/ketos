//! Provides a helper macro for extracting arguments from Ketos values.

/// Parses a set of arguments from a `&[Value]`.
///
/// ```ignore
/// // All arguments are required
/// let (name, number) = ketos_args!(args, (&str, i32));
///
/// // `number` is optional; its type will be `Option<i32>`
/// let (name, number) = ketos_args!(args, (&str [ i32 ]));
///
/// // All arguments are optional; their types will be `Option<T>`
/// let (name, number) = ketos_args!(args, [ &str, i32 ]);
/// ```
#[macro_export]
macro_rules! ketos_args {
    // All required arguments
    ( $args:expr , ( $( $ty:ty ),* ) ) => { {
        let args: &[$crate::value::Value] = $args;
        let n_args = args.len();
        let expected = 0 $( + { stringify!($ty); 1 } )*;

        if n_args != expected {
            return Err(From::from($crate::exec::ExecError::ArityError{
                name: None,
                expected: $crate::function::Arity::Exact(expected as u32),
                found: n_args as u32,
            }));
        }

        let mut _iter = args.iter();

        ( $( {
            let arg = _iter.next().unwrap();
            <$ty as $crate::value::FromValueRef>::from_value_ref(arg)?
        } , )* )
    } };
    // Optional arguments
    ( $args:expr , [ $( $ty:ty ),* ] ) => { {
        let args: &[$crate::value::Value] = $args;
        let n_args = args.len();
        let max = 0 $( + { stringify!($ty); 1 })*;

        if n_args > max {
            return Err(From::from($crate::exec::ExecError::ArityError{
                name: None,
                expected: $crate::function::Arity::Range(0, max as u32),
                found: n_args as u32,
            }));
        }

        let mut _iter = args.iter();

        ( $( {
            match _iter.next() {
                Some(arg) => Some(<$ty as
                    $crate::value::FromValueRef>::from_value_ref(arg)?),
                None => None
            }
        } , )* )
    } };
    // Some required arguments; some optional
    ( $args:expr , ( $( $r_ty:ty ),* [ $( $o_ty:ty ),* ] ) ) => { {
        let args: &[$crate::value::Value] = $args;
        let n_args = args.len();
        let min = 0 $( + { stringify!($r_ty); 1 })*;
        let optional = 0 $( + { stringify!($o_ty); 1 })*;
        let max = min + optional;

        if n_args < min || n_args > max {
            return Err(From::from($crate::exec::ExecError::ArityError{
                name: None,
                expected: $crate::function::Arity::Range(
                    min as u32, max as u32),
                found: n_args as u32,
            }));
        }

        let mut _iter = args.iter();

        ( $( {
            let arg = _iter.next().unwrap();
            <$r_ty as $crate::value::FromValueRef>::from_value_ref(arg)?
        } , )*
        $( {
            match _iter.next() {
                Some(arg) => Some(<$o_ty as
                    $crate::value::FromValueRef>::from_value_ref(arg)?),
                None => None
            }
        } , )* )
    } };
}

#[cfg(test)]
mod test {
    use error::Error;

    #[test]
    fn test_args() {
        let args = [1.into(), "sup".into(), (2, 'a').into()];

        let f = || -> Result<(), Error> {
            let (a, b, (c, d)) = ketos_args!(&args, (i32, &str, (i32, char)));

            assert_eq!(a, 1);
            assert_eq!(b, "sup");
            assert_eq!(c, 2);
            assert_eq!(d, 'a');

            Ok(())
        };

        f().unwrap();
    }

    #[test]
    fn test_empty_args() {
        let args = [];

        let f = || -> Result<(), Error> {
            let () = ketos_args!(&args, ());
            ketos_args!(&args, ());

            Ok(())
        };

        f().unwrap();
    }

    #[test]
    fn test_one_arg() {
        let args = [1.into()];

        let f = || -> Result<(), Error> {
            let (a,) = ketos_args!(&args, (i32));
            assert_eq!(a, 1);

            let (a,) = ketos_args!(&args, [i32]);
            assert_eq!(a, Some(1));

            Ok(())
        };

        f().unwrap();
    }

    #[test]
    fn test_optional_args() {
        let args = [1.into(), 2.into(), 3.into()];

        let f = || -> Result<(), Error> {
            let (a, b, c, d) = ketos_args!(&args, (i32, i32 [ i32, i32 ]));

            assert_eq!(a, 1);
            assert_eq!(b, 2);
            assert_eq!(c, Some(3));
            assert_eq!(d, None);

            let (a, b, c, d) = ketos_args!(&args, [i32, i32, i32, i32]);

            assert_eq!(a, Some(1));
            assert_eq!(b, Some(2));
            assert_eq!(c, Some(3));
            assert_eq!(d, None);

            Ok(())
        };

        f().unwrap();
    }
}
