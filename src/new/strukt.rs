// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Implementation of `strukt!`.

/// Constructs a [`New`] that builds up a struct field-by-field, in-place.
///
/// This is somewhat different from using `new::of(...).with(...)`, since you
/// can directly initialize fields using [`New`]s.
///
/// ```
/// # use moveit::{new::New, new, strukt, moveit};
/// struct Inner {
///   // ...
/// }
///
/// impl Inner {
///   pub fn new() -> impl New<Output = Self> {
///     // ...
///     # new::of(Self {})
///   }
/// }
///
/// struct Outer {
///   x: i32,
///   y: Inner,
/// }
///
/// impl Outer {
///   pub fn new() -> impl New<Output = Self> {
///     strukt!(Self {
///       x: new::of(42),
///       y: Inner::new(),
///     })
///   }
/// }
///
/// moveit!(let outer = Outer::new());
/// assert_eq!(outer.x, 42);
/// ```
///
/// If any of the passed-in constructors panics, the destructors of all fields
/// that were successfully initialized (i.e., those lexically before it) will
/// run automatically.
///
/// # Caveats
///
/// The same field cannot be assigned multiple times, like in an ordinary
/// struct literal.
///
/// ```no_compile
/// # use moveit::{new, strukt};
/// struct X { a: i32 }
///
/// let _ = strukt!(X {
///   a: new::of(1),
///   a: new::of(1),
/// });
/// ```
///
/// Currently, uninferred types and lifetimes cannot occur in the type provided
/// to `strukt!`. This is a temporary restriction that may be lifted in the
/// future.
///
/// Tuple structs are currently not supported. This is a temporary restriction
/// that may be lifted in the future.
#[macro_export]
macro_rules! strukt {
  ($strukt:path {$($field:tt $(: $value:expr)?),* $(,)?}) => {{
    extern crate core as __core;
    // We cannot follow a $path with a {, so we use an identity type alias
    // to force rustc to be ok with this. Because $strukt can capture
    // generic variables from context, we cannot store it in a type alias
    // directly.
    type __Id<T> = T;

    // rustc incorrectly thinks that this code causes anything after it
    // to be unreachable, despite the fact that it is never called!
    //
    // This is a closure so that it gets optimized out completely, beyond an
    // unused function that the linker can delete; otherwise we need to rely on
    // dead code elimination.
    #[allow(unused)]
    let _ = || __Id::<$strukt> {
      // This verifies that constructing a struct in this way, with dummy
      // values, is actually valid.
      $($field: unreachable!()),*
    };

    // This makes sure that fields are not duplicated. This is accomplished by
    // generating several functions of the same name as the fields, which will
    // clash with each other statically.
    const _: () = {
      $(fn $field() {})*
    };

    let closure = |this: __core::pin::Pin<&mut __core::mem::MaybeUninit<$strukt>>| {
      let cell = __core::cell::Cell::new(true);
      let exit_due_to_panic = &cell;
      let this = unsafe { this.get_unchecked_mut() }.as_mut_ptr();
      $(
        let field = $crate::new::__macro::memoffset::raw_field!(this, $strukt, $field);
        let value = $crate::__strukt_field!($field $(: $value)?);
        unsafe {
          $crate::new::New::new(
            value,
            $crate::new::__macro::maybe_uninit_cast(field),
          );
        }

        // When exiting due to unwinding, make sure to destroy any fields we
        // managed to initialize.
        let $field = $crate::new::__macro::Defer(move || {
          if exit_due_to_panic.get() {
            let ptr = $crate::new::__macro::mut_cast(field);
            unsafe { __core::ptr::drop_in_place(ptr); }
          }
        });
        let _allow_unused = &$field;
      )*

      exit_due_to_panic.set(false);
    };

    unsafe { $crate::new::by_raw::<$strukt, _>(closure) }
  }}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __strukt_field {
  ($field:tt: $value:expr) => {
    $value
  };
  ($field:tt) => {
    $field
  };
}

#[cfg(test)]
mod tests {
  use std::panic;

  use crate::new;
  use crate::new::Emplace as _;

  #[derive(Debug, PartialEq, Eq)]
  struct X<T> {
    a: i32,
    b: i32,
    c: T,
  }

  #[test]
  fn smoke() {
    let a = new::of(1);
    let c = Box::emplace(strukt!(X::<i32> {
      a,
      b: new::of(2),
      c: new::of(3),
    }));

    assert_eq!(&*c, &X { a: 1, b: 2, c: 3 });

    crate::moveit! {
      let y = strukt!(X::<X<i32>> {
        a: new::of(-1),
        b: new::of(42),
        c: strukt!(X::<i32> {
          a: new::of(1),
          b: new::of(2),
          c: new::of(3),
        }),
      });
    }

    assert_eq!(y.a, -1);
    assert_eq!(y.b, 42);
    assert_eq!(&y.c, &*c);
  }

  #[test]
  fn panic_safety() {
    struct MakeSureThisGetsDestroyed<'a>(&'a mut bool);
    impl Drop for MakeSureThisGetsDestroyed<'_> {
      fn drop(&mut self) {
        *self.0 = true;
      }
    }

    let mut dtor_ran = false;
    let _ = panic::catch_unwind(panic::AssertUnwindSafe(|| {
      // We need to use a box here, because unwinding out of a constructor of a
      // stack variable is poorly-supported.
      Box::emplace(strukt!(X::<MakeSureThisGetsDestroyed> {
        a: new::of(42),
        c: new::of(MakeSureThisGetsDestroyed(&mut dtor_ran)),
        b: new::by(|| panic!()),
      }));
    }));

    assert!(dtor_ran);
  }
}
