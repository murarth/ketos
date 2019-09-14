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
//! Ketos `Value` is unique, i.e. the contained `Rc` has a reference count of `1`.
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
//!
//! ## `derive(StructValue)`
//!
//! Implements [`StructValue`](https://docs.rs/ketos/*/ketos/structs/trait.StructValue.html)
//! for the given type, provided that the type implements `Clone` and all fields
//! implement `Clone`, `FromValue`, and `Into<Value>`.
//!
//! Types implementing `StructValue` can be constructed with `new` in Ketos code
//! and have their fields accessed and modified with the `.` and `.=` functions.

#![recursion_limit = "256"]

extern crate proc_macro;
extern crate proc_macro2;
#[macro_use] extern crate quote;
extern crate syn;

use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::ToTokens;
use syn::{
    parse::Error, spanned::Spanned,
    AttrStyle, Attribute, Data, DataStruct, DeriveInput, Fields,
    GenericParam, Generics, Ident, Lifetime, LifetimeDef, Lit, Meta, NestedMeta,
    Path, PathArguments, TypeGenerics, WhereClause,
};

#[proc_macro_derive(ForeignValue)]
pub fn derive_foreign_value(input: TokenStream) -> TokenStream {
    match gen_foreign_value(input) {
        Ok(output) => output.into(),
        Err(e) => e.to_compile_error().into()
    }
}

#[proc_macro_derive(FromValue)]
pub fn derive_from_value(input: TokenStream) -> TokenStream {
    match gen_from_value(input) {
        Ok(output) => output.into(),
        Err(e) => e.to_compile_error().into()
    }
}

#[proc_macro_derive(FromValueClone)]
pub fn derive_from_value_clone(input: TokenStream) -> TokenStream {
    match gen_from_value_clone(input) {
        Ok(output) => output.into(),
        Err(e) => e.to_compile_error().into()
    }
}

#[proc_macro_derive(FromValueRef)]
pub fn derive_from_value_ref(input: TokenStream) -> TokenStream {
    match gen_from_value_ref(input) {
        Ok(output) => output.into(),
        Err(e) => e.to_compile_error().into()
    }
}

#[proc_macro_derive(IntoValue)]
pub fn derive_into_value(input: TokenStream) -> TokenStream {
    let ast: DeriveInput = syn::parse(input).expect("syn::parse");

    let name = ast.ident;
    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    let expr = quote!{
        impl #impl_generics Into<::ketos::Value> for #name #ty_generics #where_clause {
            fn into(self) -> ::ketos::Value {
                ::ketos::Value::new_foreign(self)
            }
        }
    };

    expr.into()
}

#[proc_macro_derive(StructValue, attributes(ketos))]
pub fn derive_struct_value(input: TokenStream) -> TokenStream {
    match gen_struct_value(input) {
        Ok(output) => output.into(),
        Err(e) => e.to_compile_error().into()
    }
}

fn gen_foreign_value(input: TokenStream) -> Result<TokenStream2, Error> {
    let ast: DeriveInput = syn::parse(input)?;

    let name = ast.ident;
    let name_str = name.to_string();
    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    Ok(quote!{
        impl #impl_generics ::ketos::ForeignValue for #name #ty_generics #where_clause {
            fn type_name(&self) -> &'static str { #name_str }
        }
    })
}

fn gen_from_value(input: TokenStream) -> Result<TokenStream2, Error> {
    let ast: DeriveInput = syn::parse(input)?;

    let name = ast.ident;
    let name_str = name.to_string();
    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    Ok(quote!{
        impl #impl_generics ::ketos::FromValue for #name #ty_generics #where_clause {
            fn from_value(v: ::ketos::Value) -> ::std::result::Result<Self, ::ketos::ExecError> {
                match v {
                    ::ketos::Value::Foreign(fv) => {
                        match ::ketos::ForeignValue::downcast_rc(fv) {
                            ::std::result::Result::Ok(v) => {
                                match ::std::rc::Rc::try_unwrap(v) {
                                    ::std::result::Result::Ok(v) => ::std::result::Result::Ok(v),
                                    ::std::result::Result::Err(_) => ::std::result::Result::Err(
                                        ::ketos::panic(concat!(#name_str, " value is not unique")))
                                }
                            }
                            ::std::result::Result::Err(rc) => {
                                ::std::result::Result::Err(
                                    ::ketos::ExecError::expected(#name_str,
                                        &::ketos::Value::Foreign(rc)))
                            }
                        }
                    }
                    ref v => ::std::result::Result::Err(
                        ::ketos::ExecError::expected(#name_str, v))
                }
            }
        }
    })
}

fn gen_from_value_clone(input: TokenStream) -> Result<TokenStream2, Error> {
    let ast: DeriveInput = syn::parse(input)?;

    let name = ast.ident;
    let name_str = name.to_string();
    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    Ok(quote!{
        impl #impl_generics ::ketos::FromValue for #name #ty_generics #where_clause {
            fn from_value(v: ::ketos::Value) -> ::std::result::Result<Self, ::ketos::ExecError> {
                match v {
                    ::ketos::Value::Foreign(fv) => {
                        match ::ketos::ForeignValue::downcast_rc(fv) {
                            ::std::result::Result::Ok(v) => {
                                match ::std::rc::Rc::try_unwrap(v) {
                                    ::std::result::Result::Ok(v) => ::std::result::Result::Ok(v),
                                    ::std::result::Result::Err(rc) => ::std::result::Result::Ok((*rc).clone())
                                }
                            }
                            ::std::result::Result::Err(rc) => {
                                ::std::result::Result::Err(
                                    ::ketos::ExecError::expected(#name_str,
                                        &::ketos::Value::Foreign(rc)))
                            }
                        }
                    }
                    ref v => ::std::result::Result::Err(
                        ::ketos::ExecError::expected(#name_str, v))
                }
            }
        }
    })
}

fn gen_from_value_ref(input: TokenStream) -> Result<TokenStream2, Error> {
    let ast: DeriveInput = syn::parse(input)?;

    let name = ast.ident;
    let name_str = name.to_string();
    let (impl_generics, ty_generics, where_clause) = split_with_lifetime(&ast.generics);

    Ok(quote!{
        impl #impl_generics ::ketos::FromValueRef<'value> for &'value #name #ty_generics #where_clause {
            fn from_value_ref(v: &'value ::ketos::Value) -> ::std::result::Result<Self, ::ketos::ExecError> {
                if let ::ketos::Value::Foreign(fv) = v {
                    if let ::std::option::Option::Some(v) = fv.downcast_ref() {
                        return ::std::result::Result::Ok(v);
                    }
                }

                ::std::result::Result::Err(
                    ::ketos::ExecError::expected(#name_str, v))
            }
        }
    })
}

fn gen_struct_value(input: TokenStream) -> Result<TokenStream2, Error> {
    let ast: DeriveInput = syn::parse(input)?;

    let span = ast.ident.span();
    let name = ast.ident;
    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    let fields = match &ast.data {
        Data::Enum(_) =>
            return Err(Error::new(span,
                "cannot derive StructValue for enum types")),
        Data::Struct(DataStruct{fields: Fields::Unit, ..}) =>
            return Err(Error::new(span,
                "cannot derive StructValue for unit struct types")),
        Data::Struct(DataStruct{fields: Fields::Unnamed(..), ..}) =>
            return Err(Error::new(span,
                "cannot derive StructValue for tuple struct types")),
        Data::Struct(DataStruct{fields, ..}) => fields,
        Data::Union(_) =>
            return Err(Error::new(span, "cannot derive StructValue for union types")),
    };

    let name_str = name.to_string();
    let mut local = Vec::new();
    let mut field_name = Vec::new();
    let mut field_str = Vec::new();
    let mut handle_field = Vec::new();
    let mut handle_set_field = Vec::new();

    for field in fields {
        let opts = AttrOpts::parse(&field.attrs)?;

        let ident = field.ident.as_ref().unwrap();
        let ty = &field.ty;

        let field_s = opts.rename.unwrap_or_else(
            || make_field_name(&ident.to_string()));

        // A local binding is created for each field name.
        // It must not conflict with any other bindings in method implementations.
        let local_ident = Ident::new(&format!("__{}", ident), Span::call_site());

        local.push(local_ident.clone());
        field_name.push(ident.clone());
        field_str.push(field_s);

        handle_field.push(quote!{
            let v = <#ty as ::ketos::FromValue>::from_value(value)?;
            #local_ident = ::std::option::Option::Some(v);
        });

        handle_set_field.push(quote!{
            self.#ident = <#ty as ::ketos::FromValue>::from_value(value)?;
        });
    }

    // Explicitly borrow these so they may be used in multiple quote! expressions
    let field_name = &field_name;
    let local = &local;
    let field_str = &field_str;

    Ok(quote!{
        impl #impl_generics ::ketos::StructValue for #name #ty_generics #where_clause {
            fn struct_name() -> &'static str {
                #name_str
            }

            fn from_fields(scope: &::ketos::Scope,
                    def: &::std::rc::Rc<::ketos::StructDef>,
                    fields: &mut [(::ketos::Name, ::ketos::Value)])
                    -> ::std::result::Result<Self, ::ketos::Error> {
                #( let mut #local = None; )*

                let mut iter = fields.iter_mut();

                while let ::std::option::Option::Some((name, field)) = iter.next() {
                    let value = field.take();

                    scope.with_name(*name, |name_str| {
                        match name_str {
                            #( #field_str => { #handle_field } , )*
                            _ => return ::std::result::Result::Err(::ketos::Error::ExecError(
                                ::ketos::ExecError::MissingField{
                                    struct_name: def.name(),
                                    field: *name,
                                }))
                        }

                        ::std::result::Result::Ok(())
                    })?;
                }

                ::std::result::Result::Ok(#name{
                    #( #field_name : #local.ok_or_else(
                        || ::ketos::Error::ExecError(::ketos::ExecError::MissingField{
                            struct_name: def.name(),
                            field: scope.add_name(#field_str),
                        }))? ),*
                })
            }

            fn field_names() -> &'static [&'static str] {
                static FIELDS: &'static [&'static str] = &[ #( #field_str ),* ];
                FIELDS
            }

            fn get_field(&self, scope: &::ketos::Scope,
                    def: &::std::rc::Rc<::ketos::StructDef>,
                    name: ::ketos::Name)
                    -> ::std::result::Result<::ketos::Value, ::ketos::Error> {
                scope.with_name(name, |name_str| {
                    match name_str {
                        #( #field_str => { ::std::result::Result::Ok(self.#field_name.clone().into()) } , )*
                        _ => ::std::result::Result::Err(::ketos::Error::ExecError(
                            ::ketos::ExecError::FieldError{
                                struct_name: def.name(),
                                field: name,
                            }))
                    }
                })
            }

            fn replace_fields(&mut self, scope: &::ketos::Scope,
                    def: &::std::rc::Rc<::ketos::StructDef>,
                    fields: &mut [(::ketos::Name, ::ketos::Value)])
                    -> ::std::result::Result<(), ::ketos::Error> {
                for (name, value) in fields {
                    let value = value.take();

                    scope.with_name(*name, |name_str| {
                        match name_str {
                            #( #field_str => { #handle_set_field } , )*
                            _ => return ::std::result::Result::Err(::ketos::Error::ExecError(
                                ::ketos::ExecError::FieldError{
                                    struct_name: def.name(),
                                    field: *name,
                                }))
                        }

                        ::std::result::Result::Ok(())
                    })?;
                }

                ::std::result::Result::Ok(())
            }
        }
    })
}

#[derive(Default)]
struct AttrOpts {
    rename: Option<String>,
}

impl AttrOpts {
    fn parse(attrs: &[Attribute]) -> Result<AttrOpts, Error> {
        let mut opts = AttrOpts::default();

        for attr in attrs {
            if is_outer(attr.style) && path_eq(&attr.path, "ketos") {
                let meta = attr.parse_meta()?;

                match meta {
                    Meta::Word(ident) =>
                        return Err(Error::new(ident.span(),
                            "`#[ketos]` is not a valid attribute")),
                    Meta::NameValue(nv) =>
                        return Err(Error::new(nv.ident.span(),
                            "`#[ketos = ...]` is not a valid attribute")),
                    Meta::List(items) => {
                        for item in &items.nested {
                            opts.parse_item(item)?;
                        }
                    }
                }
            }
        }

        Ok(opts)
    }

    fn parse_item(&mut self, item: &NestedMeta) -> Result<(), Error> {
        match item {
            NestedMeta::Literal(lit) =>
                return Err(unexpected_meta_item(lit.span())),
            NestedMeta::Meta(item) => {
                match item {
                    Meta::NameValue(nv) => {
                        match &nv.ident.to_string()[..] {
                            "rename" => self.rename = Some(lit_str(&nv.lit)?),
                            _ => return Err(unexpected_meta_item(nv.ident.span()))
                        }
                    }
                    Meta::Word(ident) =>
                        return Err(unexpected_meta_item(ident.span())),
                    Meta::List(list) =>
                        return Err(unexpected_meta_item(list.ident.span())),
                }
            }
        }

        Ok(())
    }
}

fn path_eq(path: &Path, s: &str) -> bool {
    path.segments.len() == 1 && {
        let seg = path.segments.first().unwrap().into_value();

        match seg.arguments {
            PathArguments::None => seg.ident == s,
            _ => false
        }
    }
}

fn is_outer(style: AttrStyle) -> bool {
    match style {
        AttrStyle::Outer => true,
        _ => false
    }
}

fn lit_str(lit: &Lit) -> Result<String, Error> {
    match lit {
        Lit::Str(s) => Ok(s.value()),
        _ => Err(Error::new(lit.span(), "expected string literal"))
    }
}

fn make_field_name(name: &str) -> String {
    name.replace("_", "-")
}

fn unexpected_meta_item(span: Span) -> Error {
    Error::new(span, "unexpected meta item")
}

fn split_with_lifetime(generics: &Generics)
        -> (LtImplGenerics, TypeGenerics, Option<&WhereClause>) {
    let (_, ty_generics, where_clause) = generics.split_for_impl();

    (LtImplGenerics(generics), ty_generics, where_clause)
}

struct LtImplGenerics<'a>(&'a Generics);

impl<'a> ToTokens for LtImplGenerics<'a> {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        let mut generics = self.0.clone();

        let lt = LifetimeDef::new(Lifetime::new("'value", Span::call_site()));
        generics.params.insert(0, GenericParam::Lifetime(lt));
        let (impl_generics, _, _) = generics.split_for_impl();
        impl_generics.to_tokens(tokens);
    }
}
