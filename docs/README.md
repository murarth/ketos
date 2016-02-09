# Ketos

Ketos is a Lisp-like functional programming language, implemented in Rust
and mainly intended for extending and scripting for Rust programs.

It's not exactly a Lisp dialect. Its types and semantics are, in some cases,
closer to Rust than to Lisp.

## Syntax

Ketos syntax, the element most heavily borrowed from Lisp, consists of lists and
values. Function calls are represented as a list whose first argument is some
callable value and whose remaining arguments are passed to the function.
Every unit of Ketos code is an expression and yields a value.

```lisp
ketos=> (println "Hello, world!")
Hello, world!
()
ketos=> (+ 1 2)
3
```

### Comments

Every line starting with a `;` is considered to be a comment.

### Functions

System functions perform basic functions on standard values.

[List of system functions](functions.md)

### Operators

Operators are interpreted by the compiler at compile time. Their input syntax
often differs from normal Ketos syntax.

[List of standard operators](operators.md)

### Macros

Macros are sort of like user-defined operators. They are executed at compile
time, given the syntactical input defined in the source code. Their result is
also Ketos syntax, which is then compiled.

### Quoting

Values preceded by a `'` token are quoted, causing them to be interpreted as
literal values without being evaluated.

```lisp
ketos=> (+ 1 2)
3
ketos=> '(+ 1 2)
(+ 1 2)
```

### Quasiquoting

Values preceded by a `` ` `` token are quasiquoted. Contained elements are
treated as if quoted unless preceded by a `,` token. Elements within a quasiquoted
list that are preceded by a `,@` token must evaluate to a list. The elements
of that list are inserted into the parent list.

```lisp
ketos=> `(foo ,(+ 1 2))
(foo 3)
ketos=> `(foo ,@(concat '(1 2) '(3 4)))
(foo 1 2 3 4)
```

## Types

### Unit

Unit, or an empty list, is represented as `()`. Essentially, it's a type with
only one possible value. Functions that perform side effects often return `()`.

```lisp
ketos=> ()
()
```

### Boolean

Boolean values are `true` and `false`.

```lisp
ketos=> true
true
ketos=> false
false
ketos=> (not true)
false
```

### Integer

Ketos features arbitrary precision integers. Integer literals may be specified
in decimal, binary, octal, or hexadecimal.

```lisp
ketos=> 123
123
ketos=> 0b101010
42
ketos=> 0o100
64
ketos=> 0xdeadbeef
3735928559
```

### Float

Floating point values, specified using the Rust type `f64`.

```lisp
ketos=> 3.14159
3.14159
```

### Ratio

Arbitrary precision integer ratios.

```lisp
ketos=> 1/2
1/2
ketos=> 10/20
1/2
ketos=> 99/123
33/41
```

### List

Lists are a basic element of Ketos syntax. Normally, a list is interpreted as a
function call. In order to make a list that is interpreted as a value, the
quoting operator `'` is used. Lists can contain values of any type, including
nested lists. Only the outermost list needs to be quoted.

```lisp
ketos=> '(1 2 3)
(1 2 3)
ketos=> '(1 2/3 "foo")
(1 2/3 "foo")
ketos=> '(1 2 (3 4 (5 6)))
(1 2 (3 4 (5 6)))
```

### Name and Keyword

Names are values, too. Some languages call them an "atom." Keyword values
are similar to name values, but keywords have a special use in calling
functions. See [`define`](operators.md#define) for details.

```lisp
ketos=> 'foo
foo
ketos=> (= 'foo 'foo)
true
ketos=> (= 'foo 'bar)
false
ketos=> :foo
:foo
```

### String

Strings are encoded in UTF-8. Their syntax is identical to Rust.

```lisp
ketos=> "foo"
"foo"
ketos=> "\u{61}"
"a"
```

### Character

Characters are unicode code points. Because Ketos uses the `'` token for
quoting, character literals are prefixed with the character `#`. Otherwise,
the syntax is identical to Rust.

```lisp
ketos=> #'a'
#'a'
```

### Struct

Struct definitions and values are created through the `struct` operator
and the `new` function, respectively. Their fields are type-checked upon assignment.

```lisp
ketos=> (struct Foo ((a integer) (b string)))
Foo
ketos=> (new Foo :a 123 :b "foo")
Foo { a: 123, b: "foo" }
```

## Modules

[List of standard modules](modules.md)
