# Modules

Standard modules are built into the interpreter. Functions can be imported
from standard modules using the [`use` operator](operators.md#use).

```lisp
ketos=> (use math (sqrt))
()
ketos=> (sqrt 4.0)
2
```

## `code`

The `code` module offers facilities for inspecting compiled bytecode objects.

* `compile` returns a compiled `lambda` value from an expression.
* `disassemble` prints information about a `lambda` value to stdout.
* `documentation` returns the docstring for the named item.
* `get-const` returns a numbered const value from a `lambda` object.
* `get-value` returns a numbered enclosed value from a `lambda` object.
* `module-documentation` returns the docstring for the named module.

## `math`

The `math` module contains mathematical constants and functions.

These functions are identical to their Rust counterparts and include:
`acos`, `acosh`, `asin`, `asinh`, `atan`, `atanh`, `atan2`, `cos`, `cosh`,
`degrees`, `ln`, `log`, `log2`, `log10`, `radians`, `sin`, `sinh`, `sqrt`,
`tan`, and `tanh`.

Constants included are: `e` (Euler's number) and `pi`.

## `random`

The `random` module provides access to random number generation functions.

* `random` returns a random float value in the range `[0.0, 1.0)`.
* `shuffle` returns a given list in random order.

## `time`

The `time` module provides access to the current time.

* `utc-timestamp` returns the number of non-leap seconds observed in the UTC timezone since January 1st 1970.
* `local-timestamp` returns the number of non-leap seconds observed in the local timezone since January 1st 1970.
