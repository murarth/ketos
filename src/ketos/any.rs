//! Support for `Any` trait usage

use std::any::{Any, TypeId};

/// A helper trait that is necessary as long as `Any::get_type_id` is unstable.
pub trait AnyValue: Any {
    /// Returns the `TypeId` value for the type.
    fn type_id(&self) -> TypeId;
}

impl<T: Any> AnyValue for T {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }
}

/// Duplicate definition of `std::raw::TraitObject`, which is unstable.
#[repr(C)]
pub struct TraitObject {
    /// Data field
    pub data: *mut (),
    /// Vtable field
    pub vtable: *mut (),
}

// Implements downcast methods for a trait object type
macro_rules! impl_any_cast {
    ( $ty:ident ) => {
        impl $ty {
            /// Returns whether the contained value is of the given type.
            pub fn is<T: $ty>(&self) -> bool {
                self.type_id() == ::std::any::TypeId::of::<T>()
            }

            /// Attempts to downcast a `Box<Trait>` to a concrete type.
            pub fn downcast<T: $ty>(bx: ::std::boxed::Box<Self>)
                    -> Result<::std::boxed::Box<T>, ::std::boxed::Box<Self>> {
                if bx.is::<T>() {
                    unsafe {
                        let raw = ::std::boxed::Box::into_raw(bx);
                        Ok(::std::boxed::Box::from_raw(raw as *mut T))
                    }
                } else {
                    Err(bx)
                }
            }

            /// Returns an owned `Rc` reference to the contained value,
            /// if it is of the given type.
            pub fn downcast_rc<T: $ty>(rc: ::std::rc::Rc<Self>)
                    -> Result<::std::rc::Rc<T>, ::std::rc::Rc<Self>> {
                if rc.is::<T>() {
                    unsafe {
                        let obj: $crate::any::TraitObject = ::std::mem::transmute(rc);
                        Ok(::std::mem::transmute(obj.data))
                    }
                } else {
                    Err(rc)
                }
            }

            /// Returns a reference to the contained value, if it is of the given type.
            pub fn downcast_ref<T: $ty>(&self) -> Option<&T> {
                if self.is::<T>() {
                    unsafe {
                        let obj: $crate::any::TraitObject = ::std::mem::transmute(self);
                        Some(&*(obj.data as *const T))
                    }
                } else {
                    None
                }
            }

            /// Returns a mutable reference to the contained value,
            /// if it is of the given type.
            pub fn downcast_mut<T: $ty>(&mut self) -> Option<&mut T> {
                if self.is::<T>() {
                    unsafe {
                        let obj: $crate::any::TraitObject = ::std::mem::transmute(self);
                        Some(&mut *(obj.data as *mut T))
                    }
                } else {
                    None
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::AnyValue;

    use std::fmt;
    use std::rc::Rc;

    trait SomeTrait: AnyValue + fmt::Debug {}

    impl_any_cast!{ SomeTrait }

    #[derive(Debug)]
    struct Dummy {
        a: i32,
    }

    #[derive(Debug)]
    struct Dumber;

    impl SomeTrait for Dummy { }

    impl SomeTrait for Dumber { }

    #[test]
    fn test_downcast() {
        let a: Box<SomeTrait> = Box::new(Dummy{a: 0});

        let b = SomeTrait::downcast::<Dumber>(a).unwrap_err();
        let c = SomeTrait::downcast::<Dummy>(b).unwrap();

        assert_eq!(c.a, 0);
    }

    #[test]
    fn test_downcast_rc() {
        let a: Rc<SomeTrait> = Rc::new(Dummy{a: 0});

        let b = SomeTrait::downcast_rc::<Dumber>(a).unwrap_err();
        let c = SomeTrait::downcast_rc::<Dummy>(b).unwrap();

        assert_eq!(c.a, 0);
    }

    #[test]
    fn test_downcast_ref() {
        let mut a: Box<SomeTrait> = Box::new(Dummy{a: 0});

        {
            let r = a.downcast_mut::<Dummy>().unwrap();
            r.a = 123;
        }

        let r = a.downcast_ref::<Dummy>().unwrap();

        assert_eq!(r.a, 123);
    }
}
