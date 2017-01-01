# Functions

These system functions are defined within the Ketos interpreter.
They are available, by default, in any scope.

## Arithmetic Functions

Basic arithmetic functions include `+`, `-`, `*`, `/`, `//`, `^`, and `rem`.
They perform the same operation as their Rust counterparts. The only exception
being that, if the given values of different numeric types, the values will
be coerced according to these rules:

* For all operations:
  * `integer` and `float` => `float`
  * `integer` and `ratio` => `ratio`
  * `ratio` and `float` => `float`
* For division:
  * `integer` and `integer` will result in `ratio` if the two values
    cannot be evenly divided.
* For exponentation:
  * `ratio` and `ratio` results in a `float`
  * If the right-hand side is a negative `integer`, the result is always `float`

The `//` function, which does not exist in Rust, is the "floor division"
function. It will divide its arguments as normal and return the `floor`
of the value.

## Bitwise Functions

Bitwise functions `<<` and `>>` are supported.

## Comparison Functions

The equality function `=`, inequality function `/=` and ordered comparison
functions, `<`, `<=`, `>`, and `>=` are supported. With the exception of above
numeric coercion rules, these functions will produce an error if two values of
different types are received.

The `zero` function tests whether given values are equal to zero.

## Numeric Functions

* `abs` returns the absolute value of a numeric value.
* `ceil` rounds a numeric value toward positive infinity.
* `floor` rounds a numeric value toward negative infinity.
* `trunc` rounds a numeric value toward zero.
* `int` rounds a numeric value toward zero and returns an `integer`.
* `float` returns a numeric value converted into a `float`.
* `inf` returns whether a given `float` value is infinite; given no arguments,
  it will instead return a value of positive infinity.
* `nan` returns whether a given `float` value is `NaN`; given no arguments,
  it will instead return a value of `NaN`.
* `denom` returns the denominator of a rational value.
* `numer` returns the numerator of a rational value.
* `fract` returns the fractional portion of a `ratio` or `float`.
* `rat` will convert a value to a `ratio` or compose a `ratio` from two `integer`
  values.
* `recip` returns the reciprocal of a numeric value.

## List Functions

* `append` appends a value to a list, e.g. `(append list value)`.
* `elt` returns the nth element of a list, e.g. `(elt list n)`.
* `concat` concatenates each given list value.
* `join` joins together a series of lists using the first argument as separator.
* `len` returns the length of a list.
* `slice` returns a subslice of a list value, e.g. `(slice list begin end)`.
* `first` returns the first element of a list.
* `second` returns the second element of a list.
* `last` returns the last element of a list.
* `init` returns all elements until the last element of a list.
* `tail` returns all elements after the first element of a list.
* `list` evaluates each of its arguments and return them as a list.
* `reverse` returns a list with elements in reverse order.

## String Functions

* `concat` concatenates a series of string or char values.
* `join` joins together a series of strings using the first argument as separator.
* `len` returns the length, in bytes, of a string.
* `chars` returns a list of char values for each successive char in a string.
* `string` returns a char value as a string.

## Struct Functions

* `new` returns a new struct value with named field values,
  e.g. `(new Foo :a 1 :b "foo")`.
* `is-instance` returns whether a given struct value is an instance of
  a given struct-def, e.g. `(is-instance Foo foo-value)`.
* `.` returns a named field of a struct value, e.g. `(. struct :foo)`.
* `.=` returns a struct value with the named field assigned to a new value,
  e.g. `(.= struct :foo bar)`. Accepts many keyword-value pairs.

## Other Functions

* `bytes`, converts a string or list of integers into a byte string.
* `id`, the identity function, returns its argument as-is.
* `type-of` returns a name value indicating the type of its argument.
* `is` returns whether the type of value matches the given type,
  e.g. `(is 'integer 0)`.  
  Additionally, the type `'number` will match any numeric type.
* `null` returns whether the given value is `()`.
* `format` returns a formatted string; see [string_formatting.md]
* `print` prints a formatted string to stdout; see [string_formatting.md]
* `println` prints a formatted string to stdout, followed by a newline;
  see [string_formatting.md]
* `panic` causes a panic; similar in concept to a Rust panic.
* `xor` returns the logical XOR of two `bool` values
* `not` returns the logical NOT of a `bool` value
