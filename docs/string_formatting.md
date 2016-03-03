# String Formatting

Standard string formatting functions `format`, `print`, and `println` are based
on Common Lisp's `format` function. These functions accept a format string,
containing text and formatting directives, and a series of arguments processed
according to the format string.

The `format` function returns formatted output as a string; `print` writes
formatted output to stdout; and `println` writes to stdout, followed by a newline.

Formatting string directives may consume an input argument in a variety of ways,
including conditional, iteration, and transformation operations.

Formatting directives consist of a tilde (`~`), followed by optional flags
indicated by the `:` and `@` characters, zero or more optional comma-separated
parameters, concluded with a single character.

Directive parameters may be literal numbers; character constants, preceded by
a `'`; the character `v`, which indicates to consume an input argument for the
parameter value; or the character `#`, which indicates to use the number of
remaining arguments as the parameter value.

## `a` - Aesthetic

Formats a value in a manner similar to the Rust `fmt::Display` trait.

Parameters are *min-col*,*col-inc*,*min-pad*,*pad-char*.

The string is right-padded (or left-padded if the `@` flag is present) with
*min-pad* *pad-char*s. Then, *col-inc* *pad-char*s are inserted until the
result is at least *min-col* chars long.  
*min-col* and *min-pad* default to `0`; *col-inc* defaults to `1`; *pad-char*
defaults to space.

```lisp
(format "~a" "foo") => "foo"
(format "~10a" "foo") => "foo       "
(format "~10@a" "foo") => "       foo"
```

## `s` - Standard

Formats a value in a manner similar to the Rust `fmt::Debug` trait.

Parameters are identical to the `a` directive.

```lisp
(format "~s" #'a') => "#'a'"
```

## `c` - Character

Outputs the value of a character.

```lisp
(format "~c~c~c" #'a' #'b' #'c') => "abc"
```

## `f` - Float

Formats a floating point value in standard notation.

Parameters are *width*,*precision*,*pad-char*.

*width* and *precision* are passed to the Rust float formatter.  
*pad-char* is used to pad the result and defaults to space.

If the `@` flag is present, the sign of the value is always displayed.

```lisp
(format "~5,2f" 3.14159) => " 3.14"
```

## `e` - Exponent

Formats a floating point value in exponent notation.

Parameters are identical to `f` directive.

## `d`, `b`, `o`, `x` - Integer

The `d`, `b`, `o`, and `x` directives format an integer in decimal, binary,
octal, or hexadecimal, respectively.

Parameters are *min-col*,*pad-char*,*comma-char*,*comma-interval*.

The result is padded with *pad-char* to at least *min-col* characters.  
*min-col* defaults to `0`; *pad-char* defaults to space.

If the `@` flag is present, the sign of the value is always displayed.

If the `:` flag is present, *comma-char* will be inserted into the result
every *comma-interval* digits, starting from the least significant digit.  
*comma-char* defaults to `,`; *comma-interval* defaults to `3`.

## `r` - Radix

If given at least one parameter, the `r` directive will format an integer
in a given base in the range `[2, 36]`. Remaining parameters are handled as
for the above integer formatting directives.

With no parameters, `~r` will produce the following output:

* `~r` will output the cardinal; e.g. `one`, `two`, etc.
* `~:r` will output the ordinal; e.g. `first`, `second`, etc.
* `~@r` will output Roman numerals; e.g. `4` as `IV`.
* `~@:r` will output old Roman numerals; e.g. `4` as `IIII`.

## `p` - Plural

Formats a standard English plural or singular suffix based on a numeric value.
If the value is `1`, nothing is output; otherwise `s` is output.
When the `@` flag is present, `y` is output for a value of `1` and `ies` is
output for any other value.

When the `:` flag is present, the directive will first back up one argument
before consuming an argument.

```lisp
(format "~d friend~:p, ~d enem~:@p" 1 2) => "1 friend, 2 enemies"
(format "~d friend~:p, ~d enem~:@p" 2 1) => "2 friends, 1 enemy"
(format "~d friend~:p, ~d enem~:@p" 3 0) => "3 friends, 0 enemies"
```

## `t` - Tabulate

Spaces over to a given column.

Parameters are *col-num*,*col-inc*.  
The directive will space over to at least *col-num*th column, in *col-inc*
increments.

If the `@` flag is present, the parameters are *col-rel*,*col-inc*.  
the directive will output *col-rel* spaces, then output enough spaces to advance
to a column that is a multiple of *col-inc*, if necessary.

## `z` - Pretty Print

Formats a value in a human-readable fashion, inserting newlines and indentation
into nested lists.

Accepts a single parameter, *indent*.  
Values within lists are indented, starting at *indent* characters from the
first column. The top level value is not indented.

```lisp
(println "~z"    '(foo (bar (baz))))
(println "  ~2z" '(foo (bar (baz))))
```

## `?` - Indirection

The directive will consume a string and a list, processing the string as a format
string and using the list as arguments.

If the `@` flag is present, only a format string argument is consumed and the
arguments from the current formatting operation are used.

## `*` - Goto

This directive adjusts which input argument will be consumed by the next
formatting directive.

A single integer parameter, *n*, is accepted. The directive will advance *n*
arguments forward. If the `:` flag is present, the directive will instead move
backward.

If the `@` flag is present, the integer argument is taken as an absolute index
pointing to the next argument to be consumed.

## `<` / `>` - Justification

Formats contained directives and left-, right-, or center-justifies resulting
output.

The contents of `~<` and `~>` may be split into segments using `~;`, in which
case, spacing is evenly divided between segments.

With no flags, the leftmost text is left-justified and the rightmost text is
right-justified; if there is only one segment, it is right-justified.
If the `:` flag is present, spacing is added before the first segment.
If the `@` flag is present, spacing is added after the last segment.

Parameters are *min-col*,*col-inc*,*min-pad*,*pad-char*.  
The text is padded with *min-pad* instances of *pad-char*. Then, *col-inc*
padding characters are added until *min-col* is reached.  
*min-col* and *min-pad* default to `0`; *col-inc* defaults to `1`;
*pad-char* defaults to space.

## `(` / `)` - Case conversion

Performs case conversion on resulting text.

* `~(...~)` transforms all letters to lowercase.
* `~@(...~)` capitalizes the first letter.
* `~:(...~)` capitalizes the first letter of each word.
* `~@:(...~)` transforms all letters to uppercase.

## `[` / `]` - Conditional

Given no flags, the directive consumes an integer argument and selects one of
the contained branches, separated by `~;`, starting at `0`. If the argument
index exceeds the branches contained, no text is output. However, the last
branch may be indicated as a default branch by preceding it with `~:;`.  
If a parameter is given, it is used in place of consuming a value.

If the `:` flag is present, a boolean value is consumed. The first branch
is output if the value is `false`; otherwise, the second branch is output.

If the `@` flag is present, the next argument is tested. If it is `()`,
nothing is output and the value is consumed; otherwise, the value is not
consumed and the sole contained clause is output. Therefore, the clause
should typically consume exactly one argument.

## `{` / `}` - Iteration

Consumes a list value and outputs the contained directives until the list is
empty. Each iteration may consume as many arguments as it desires. The `~^`
directive may be used to terminate iteration if no arguments remain.

If the `:` flag is present, the consumed list is instead a list of sublists.
The values of each sublist are made available to each iteration.

If the `@` flag is present, remaining arguments are used instead of a single
list argument.

If both `:` and `@` flags are present, the remaining arguments are used, each
required to be a list.

## `^` - Terminate

Terminates a grouping directive if no arguments remain to be consumed.

If `~^` is used within a `~:{...~}` group, only the current iteration is
terminated. Use `~:^` instead to terminate the entire iteration.

## `|` - Page

Inserts a page feed character (`\x0c`). If a parameter *n* is given,
inserts *n* page feed characters.

## `%` - Newline

Inserts a newline character (`\n`). If a parameter *n* is given,
inserts *n* newline characters.

## `&` - Fresh line

If output will be written an empty line, this directive does nothing;
otherwise, it outputs a newline (`\n`). If a parameter *n* is given,
it will then output *n*-1 newlines.

## `\n` - Newline continuation

`~` followed by a newline character (`\n`) will consume the newline and any
following non-newline whitespace characters.

## `~` - Tilde

Outputs a literal tilde character (`~`). If a parameter *n* is given,
outputs *n* tilde characters.
