# `ketos_derive`

Provides a set of custom `#[derive(...)]` macros for convenience when using Ketos.

One or more of the following names can be added to the `derive` attribute of
any struct or enum value. For example:

```rust
extern crate ketos;
#[macro_use] extern crate ketos_derive;

#[derive(Clone, Debug, ForeignValue, FromValue, IntoValue)]
struct Foo {
    // ...
}
```

## `derive(ForeignValue)`

Implements [`ForeignValue`](https://docs.rs/ketos/*/ketos/value/trait.ForeignValue.html)
for the given type. The only method implemented by this macro is `type_name`.
All other methods retain their default implementations.

The `ForeignValue` trait must be implemented (either manually or using this `derive`)
for any of the other `derive` implementations to succeed.

## `derive(FromValue)`

Implements [`FromValue`](https://docs.rs/ketos/*/ketos/value/trait.FromValue.html)
for the given type.

The generated implementation requires that the instance of the type held by the
Ketos `Value` is unique, i.e. that the contained `Rc` has a reference count of `1`.

If your type implements `Clone`, `derive(FromValueClone)` will instead generate
an implementation of `FromValue` that clones the contained value, if necessary.

## `derive(FromValueClone)`

Implements [`FromValue`](https://docs.rs/ketos/*/ketos/value/trait.FromValue.html)
for the given type, provided that the type implements the `Clone` trait.

If the value contained in the Ketos `Value` is not unique, the result will be
a clone of the contained value.

## `derive(FromValueRef)`

Implements [`FromValueRef`](https://docs.rs/ketos/*/ketos/value/trait.FromValueRef.html)
for the given type.

## `derive(IntoValue)`

Implements `Into<Value>` for the given type.
