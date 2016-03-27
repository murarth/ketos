# Operators

Operators are special routines recognized at compile-time.

## `apply`

```
(apply function [ arguments ... ] argument-list)
```

The `apply` operator calls a function with a given series of arguments.
The argument list consists of any positional arguments except for the last
argument to `apply`, plus the final, required list argument, which is
concatenated to positional arguments.

```lisp
(apply + 1 2 3 '(4 5 6))
```

## `const`

```
(const name [docstring] expression)
```

The `const` operator defines a compile-time constant value in the global scope.
Any code referencing the constant by name will use the constant value directly,
without performing a name lookup operation at runtime.

The expression must be a compile-time constant, which will not vary from one
execution of the program to the next. Most system functions can be executed
at compile time if all of the arguments are constant expressions.

The optional parameter *docstring* will supply documentation for the item.

```lisp
(const one 1)
(const two 2)
(const three (+ one two))
```

## `do`

```
(do [ expressions ... ])
```

The `do` operator executes multiple expressions and yields the value of the
final expression. This is useful for calling functions with side effects.

```lisp
(do
  (print "Hello,")
  (print " world")
  (println "!"))
```

## `let`

```
(let ( [ ( name expression ) ... ] ) body)
```

The `let` operator defines a series of local bindings for the duration of the
execution of its body expression.

```lisp
(let ((a 1)
      (b 2))
  (+ a b))
```

## `define`

```
(define name [docstring] expression)

(define (name [ arguments ...
                [ :optional arguments ... ]
                [ :key arguments ... ]
                [ :rest rest-argument ]
                ] ) expression)
```

The `define` operator adds a value or compiled function to the global scope.

```lisp
; Associates the global name `foo` with the value `123`.
(define foo 123)

; Associates the global name `bar` with a function that returns twice its input.
(define (bar a) (* a 2))
```

When defining a function, if the keyword `:optional` is present in the argument
list, all following arguments will be optional. If the keyword `:key` is present,
all following arguments will be optional keyword arguments. If the keyword
`:rest` is present, the following name will contain any free arguments remaining.

Optional and keyword arguments may be omitted when calling a function.
If an optional or keyword value is not supplied its value will be `()`.
A default value can be given when the function is defined.

```lisp
; Defines a function taking an optional argument, a.
(define (foo :optional a) a)

; Calls foo with no arguments. The value of `a` will be `()`.
(foo)
; Calls foo with arguments. The value of `a` will be `123`.
(foo 123)

; Defines a function taking an optional keyword argument, a,
; whose value defaults to `1`.
(define (bar :key (a 1)) a)

; Calls bar with no arguments. The value of `a` will be `1`.
(bar)
; Calls bar with keyword argument. The value of `a` will be `2`.
(bar :a 2)
```

The optional parameter *docstring* will supply documentation for the item.

## `macro`

```
(macro (name [ arguments ... ]) [docstring] expression)
```

The `macro` operator defines a compile-time macro. A macro behaves in all
respects as any other function, except that it is executed at compile time
and is expected to return code which is then further compiled.

The optional parameter *docstring* will supply documentation for the item.

## `struct`

```
(struct name [docstring] ( [ ( name type-name ) ... ] ))
```

The `struct` operator creates a struct definition and adds it to the global scope.
The fields of the struct definition will be required to have the given types.

```lisp
(struct Foo ((a integer)
             (b string)))
```

The optional parameter *docstring* will supply documentation for the item.

## `if`

```
(if condition
  then-case
  [ else-case ])
```

The `if` operator evaluates its first argument, then evaluates only one of the
given branches, depending on the result. The "else" branch may be omitted,
in which case, `if` will yield `()` when the condition is `false`.

```lisp
(if (< a b)
  a
  b)
```

## `and` / `or`

```
(and [ expression ... ])
(or [ expression ... ])
```

The `and` and `or` operators evaluate their arguments, applying logical AND/OR
short-circuiting rules.

## `case`

```
(case expression
  [ ( ( [ expression ... ] ) branch ) ... ]
  [ ( else else-branch ) ] )
```

The `case` operator performs basic pattern matching by testing for equality
with given sets of values. The name `else` may be used for the last case,
as a catch-all branch.

```lisp
(case foo
  ((0 2 4 6 8) 'even)
  ((1 3 5 7 9) 'odd)
  (else        'other))
```

## `cond`

```
(cond
  [ ( predicate branch ) ... ]
  [ ( else else-branch ) ] )
```

The `cond` operator evaluates a series of predicates and executes the branch
for the first predicate which evaluates true. The name `else` may be used for
the last case, as a catch-all branch.

```lisp
(cond
  ((< n 0) 'negative)
  ((> n 0) 'positive)
  (else    'zero))
```

## `lambda`

```
(lambda ( [ arguments ... ] ) [docstring] expression)
```

The `lambda` operator creates a function which may enclose one or more local
value bindings from the surrounding scope.

```
(define (adder a)
  (lambda (b) (+ a b)))
```

The optional parameter *docstring* will supply documentation for the item.

## `export`

```
(export ( [ name ... ] ))
```

The `export` operator exports a series of names from a module's global scope.
Exported names may be imported from another module using the `use` operator.

## `use`

```
(use module-name { :all | ( [ name ... ] ) })
```

The `use` operator loads a module and imports a series of named constants,
macros, or values from its global scope. `:all` may be used in place of a name
list to import all public names from a module.
