//! Derive traits for Ketos scripting language
//!
//! Provides a set of custom `#[derive(...)]` macros for convenience when using Ketos.
//!
//! One or more of the following names can be added to the `derive` attribute of
//! any struct or enum value. For example:
//!
//! ```ignore
//! extern crate ketos;
//! #[macro_use] extern crate ketos_derive;
//!
//! #[derive(Clone, Debug, ForeignValue, FromValue, IntoValue)]
//! struct Foo {
//!     // ...
//! }
//! ```
//!
//! ## `derive(ForeignValue)`
//!
//! Implements [`ForeignValue`](https://docs.rs/ketos/*/ketos/value/trait.ForeignValue.html)
//! for the given type. The only method implemented by this macro is `type_name`.
//! All other methods retain their default implementations.
//!
//! The `ForeignValue` trait must be implemented (either manually or using this `derive`)
//! for any of the other `derive` implementations to succeed.
//!
//! ## `derive(FromValue)`
//!
//! Implements [`FromValue`](https://docs.rs/ketos/*/ketos/value/trait.FromValue.html)
//! for the given type.
//!
//! The generated implementation requires that the instance of the type held by the
//! Ketos `Value` is unique, i.e. that the contained `Rc` has a reference count of `1`.
//!
//! If your type implements `Clone`, `derive(FromValueClone)` will instead generate
//! an implementation of `FromValue` that clones the contained value, if necessary.
//!
//! ## `derive(FromValueClone)`
//!
//! Implements [`FromValue`](https://docs.rs/ketos/*/ketos/value/trait.FromValue.html)
//! for the given type, provided that the type implements the `Clone` trait.
//!
//! If the value contained in the Ketos `Value` is not unique, the result will be
//! a clone of the contained value.
//!
//! ## `derive(FromValueRef)`
//!
//! Implements [`FromValueRef`](https://docs.rs/ketos/*/ketos/value/trait.FromValueRef.html)
//! for the given type.
//!
//! ## `derive(IntoValue)`
//!
//! Implements `Into<Value>` for the given type.

#![recursion_limit = "128"]

extern crate proc_macro;
#[macro_use] extern crate quote;
extern crate syn;

use proc_macro::TokenStream;
use quote::{ToTokens, Tokens};
use syn::{Generics, TyGenerics, WhereClause};

#[proc_macro_derive(ForeignValue)]
pub fn derive_foreign_value(input: TokenStream) -> TokenStream {
    let ast = syn::parse_derive_input(&input.to_string())
        .expect("parse_derive_input");

    let name = ast.ident;
    let name_str = syn::Lit::from(name.to_string());
    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    let expr = quote!{
        impl #impl_generics ::ketos::ForeignValue for #name #ty_generics #where_clause {
            fn type_name(&self) -> &'static str { #name_str }
        }
    };

    expr.to_string().parse().expect("parse quote!")
}

#[proc_macro_derive(FromValue)]
pub fn derive_from_value(input: TokenStream) -> TokenStream {
    let ast = syn::parse_derive_input(&input.to_string())
        .expect("parse_derive_input");

    let name = ast.ident;
    let name_str = syn::Lit::from(name.to_string());
    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    let expr = quote!{
        impl #impl_generics ::ketos::FromValue for #name #ty_generics #where_clause {
            fn from_value(v: ::ketos::Value) -> Result<Self, ::ketos::ExecError> {
                match v {
                    ::ketos::Value::Foreign(fv) => {
                        match ::ketos::ForeignValue::downcast(fv) {
                            Ok(v) => {
                                match ::std::rc::Rc::try_unwrap(v) {
                                    Ok(v) => Ok(v),
                                    Err(_) => Err(::ketos::panic(
                                        concat!(#name_str, " value is not unique")))
                                }
                            }
                            Err(rc) => {
                                Err(::ketos::ExecError::expected(#name_str,
                                    &::ketos::Value::Foreign(rc)))
                            }
                        }
                    }
                    ref v => Err(::ketos::ExecError::expected(#name_str, v))
                }
            }
        }
    };

    expr.to_string().parse().expect("parse quote!")
}

#[proc_macro_derive(FromValueClone)]
pub fn derive_from_value_clone(input: TokenStream) -> TokenStream {
    let ast = syn::parse_derive_input(&input.to_string())
        .expect("parse_derive_input");

    let name = ast.ident;
    let name_str = syn::Lit::from(name.to_string());
    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    let expr = quote!{
        impl #impl_generics ::ketos::FromValue for #name #ty_generics #where_clause {
            fn from_value(v: ::ketos::Value) -> Result<Self, ::ketos::ExecError> {
                match v {
                    ::ketos::Value::Foreign(fv) => {
                        match ::ketos::ForeignValue::downcast(fv) {
                            Ok(v) => {
                                match ::std::rc::Rc::try_unwrap(v) {
                                    Ok(v) => Ok(v),
                                    Err(rc) => Ok((*rc).clone())
                                }
                            }
                            Err(rc) => {
                                Err(::ketos::ExecError::expected(#name_str,
                                    &::ketos::Value::Foreign(rc)))
                            }
                        }
                    }
                    ref v => Err(::ketos::ExecError::expected(#name_str, v))
                }
            }
        }
    };

    expr.to_string().parse().expect("parse quote!")
}

#[proc_macro_derive(FromValueRef)]
pub fn derive_from_value_ref(input: TokenStream) -> TokenStream {
    let ast = syn::parse_derive_input(&input.to_string())
        .expect("parse_derive_input");

    let name = ast.ident;
    let name_str = syn::Lit::from(name.to_string());
    let (impl_generics, ty_generics, where_clause) = split_with_lifetime(&ast.generics);

    let expr = quote!{
        impl #impl_generics ::ketos::FromValueRef<'value> for &'value #name #ty_generics #where_clause {
            fn from_value_ref(v: &'value ::ketos::Value) -> Result<Self, ::ketos::ExecError> {
                if let ::ketos::Value::Foreign(ref fv) = *v {
                    if let Some(v) = fv.downcast_ref() {
                        return Ok(v);
                    }
                }

                Err(::ketos::ExecError::expected(#name_str, v))
            }
        }
    };

    expr.to_string().parse().expect("parse quote!")
}

#[proc_macro_derive(IntoValue)]
pub fn derive_into_value(input: TokenStream) -> TokenStream {
    let ast = syn::parse_derive_input(&input.to_string())
        .expect("parse_derive_input");

    let name = ast.ident;
    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    let expr = quote!{
        impl #impl_generics Into<::ketos::Value> for #name #ty_generics #where_clause {
            fn into(self) -> ::ketos::Value {
                ::ketos::Value::new_foreign(self)
            }
        }
    };

    expr.to_string().parse().expect("parse quote!")
}

fn split_with_lifetime(generics: &Generics)
        -> (LtImplGenerics, TyGenerics, &WhereClause) {
    let (_, ty_generics, where_clause) = generics.split_for_impl();

    (LtImplGenerics(generics), ty_generics, where_clause)
}

struct LtImplGenerics<'a>(&'a Generics);

impl<'a> ToTokens for LtImplGenerics<'a> {
    fn to_tokens(&self, tokens: &mut Tokens) {
        let mut generics = self.0.clone();

        generics.lifetimes.insert(0, syn::LifetimeDef::new("'value"));
        let (impl_generics, _, _) = generics.split_for_impl();
        impl_generics.to_tokens(tokens);
    }
}
