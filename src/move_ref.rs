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

//! Move references.
//!
//! A move reference represents an owned value that is stored "somewhere else".
//! We own the value, not the storage.
//!
//! A [`MoveRef<'a, T>`] represents a *permanent* unique reference to `T` for
//! the lifetime `'a`: it is the longest-lived *possible* reference to the
//! pointee, making it closer to a [`Box<T>`]
//!
//! Like [`&mut T`] but unlike [`Box<T>`], a [`MoveRef<T>`] is not responsible
//! for destroying its storage, meaning that it is storage agnostic. The storage
//! might be on the stack *or* on the heap; some RAII value on the stack is
//! responsible for destroying just the storage, once the [`MoveRef<T>`] itself
//! is gone.
//!
//! The main mechanism for obtaining [`MoveRef`]s is the [`moveit!()`] macro,
//! which is analogous to a theoretical `&move expr` operator. This macro
//! wraps [`DerefMove`], much like `&mut expr` wraps [`DerefMut`].
//!
//! Implementing [`DerefMove`] is a delicate affair; its documentation details
//! exactly how it should be done.

use core::marker::Unpin;
use core::mem;
use core::ops::Deref;
use core::ops::DerefMut;
use core::pin::Pin;
use core::ptr;

#[cfg(doc)]
use {
  alloc::{boxed::Box, rc::Rc, sync::Arc},
  core::mem::{ManuallyDrop, MaybeUninit},
};

use crate::slot::DroppingSlot;

/// A `MoveRef<'a, T>` represents an owned `T` whose storage location is valid
/// but unspecified.
///
/// See [the module documentation][self] for more details.
pub struct MoveRef<'a, T: ?Sized> {
  ptr: &'a mut T,
}

impl<'a, T: ?Sized> MoveRef<'a, T> {
  /// Creates a new `MoveRef<T>` out of a mutable reference.
  ///
  /// # Safety
  ///
  /// `ptr` must satisfy the *longest-lived* criterion: after the return value
  /// goes out of scope, `ptr` must also be out-of-scope. Calling this function
  /// correctly is non-trivial, and should be left to [`moveit!()`] instead.
  ///
  /// In particular, if `ptr` outlives the returned `MoveRef`, it will point
  /// to dropped memory, which is UB.
  #[inline]
  pub unsafe fn new_unchecked(ptr: &'a mut T) -> Self {
    Self { ptr }
  }

  /// Converts a `MoveRef<T>` into a `Pin<MoveRef<T>>`.
  ///
  /// Because we own the referent, we are entitled to pin it permanently. See
  /// [`Box::into_pin()`] for a standard-library equivalent.
  #[inline]
  pub fn into_pin(this: Self) -> Pin<Self> {
    unsafe { Pin::new_unchecked(this) }
  }

  /// Returns this `MoveRef<T>` as a raw pointer, without creating an
  /// intermediate reference.
  ///
  /// The usual caveats for casting a reference to a pointer apply.
  #[inline]
  pub fn as_ptr(this: &Self) -> *const T {
    this.ptr
  }

  /// Returns this `MoveRef<T>` as a raw mutable pointer, without creating an
  /// intermediate reference.
  ///
  /// The usual caveats for casting a reference to a pointer apply.
  #[inline]
  pub fn as_mut_ptr(this: &mut Self) -> *mut T {
    this.ptr
  }
}

// Extremely dangerous casts used by DerefMove below.
impl<'a, T> MoveRef<'a, T> {
  /// Consumes `self`, blindly casting the inner pointer to `U`.
  unsafe fn cast<U>(self) -> MoveRef<'a, U> {
    let mr = MoveRef {
      ptr: &mut *(self.ptr as *mut T as *mut U),
    };
    mem::forget(self);
    mr
  }
}

impl<'a, T> MoveRef<'a, T> {
  /// Consume the `MoveRef<T>`, returning the wrapped value.
  #[inline]
  pub fn into_inner(this: Self) -> T {
    let val = unsafe { ptr::read(this.ptr) };
    mem::forget(this);
    val
  }
}

impl<T: ?Sized> Deref for MoveRef<'_, T> {
  type Target = T;

  #[inline]
  fn deref(&self) -> &Self::Target {
    self.ptr
  }
}

impl<T: ?Sized> DerefMut for MoveRef<'_, T> {
  #[inline]
  fn deref_mut(&mut self) -> &mut Self::Target {
    self.ptr
  }
}

impl<T: ?Sized> Drop for MoveRef<'_, T> {
  #[inline]
  fn drop(&mut self) {
    unsafe { ptr::drop_in_place(self.ptr) }
  }
}

impl<'a, T> From<MoveRef<'a, T>> for Pin<MoveRef<'a, T>> {
  #[inline]
  fn from(x: MoveRef<'a, T>) -> Self {
    MoveRef::into_pin(x)
  }
}

/// Moving dereference operations.
///
/// This trait is the `&move` analogue of [`Deref`], for taking a pointer that
/// is the *sole owner* its pointee and converting it to a [`MoveRef`]. In
/// particular, a pointer type `P` owns its contents if dropping it would cause
/// its pointee's destructor to run.
///
/// For example:
/// - [`MoveRef<T>`] implements `DerefMove` by definition.
/// - [`Box<T>`] implements `DerefMove`, since it drops the `T` in its
///   destructor.
/// - [`&mut T`] does *not* implement `DerefMove`, because it is
///   necessarily a borrow of a longer-lived, "truly owning" reference.
/// - [`Rc<T>`] and [`Arc<T>`] do *not* implement `DerefMove`, because even
///   though they own their pointees, they are not the *sole* owners. Dropping
///   a reference-counted pointer need not run the destructor if other pointers
///   are still alive.
/// - [`Pin<P>`] for `P: DerefMove` implements `DerefMove` only when
///   `P::Target: Unpin`, since `DerefMove: DerefMut`. To
///
/// # Principle of Operation
///
/// Unfortunately, because we don't yet have language support for `&move`, we
/// need to break the implementation into two steps:
/// - Inhibit the "inner destructor" of the pointee, so that the smart pointer
///   is now managing dumb bytes. This is usually accomplished by converting the
///   pointee type to [`MaybeUninit<T>`].
/// - Extract a [`MoveRef`] out of the "deinitialized" pointer.
///
/// The first part of this consists of converting the pointer into the
/// "partially deinitialized" form, represented by the type
/// [`DerefMove::Storage`]: it is the pointer as "pure storage".
///
/// This pointer should be placed into the [`DroppingSlot`] passed into
/// `deref_move`, so that it has a fixed lifetime for the duration of the frame
/// that the [`MoveRef`] will exist for.
///
/// The mutable reference returned by the [`DroppingSlot`] should then be
/// converted into a [`MoveRef`]. The end result is that the [`DroppingSlot`]
/// owns the "outer" part of the pointer, while the [`MoveRef`] owns the "inner"
/// part. The `'frame` lifetime enforces the correct destruction order of these
/// two parts, since the [`MoveRef`] borrows the [`DroppingSlot`].
///
/// The [`moveit!()`] macro helps by constructing the [`DroppingSlot`] for you.
///
/// ## Worked Example: [`Box<T>`]
///
/// To inhibit the inner destructor of [`Box<T>`], we can use `Box<MaybeUninit<T>>`
/// as [`DerefMove::Storage`]. [`MaybeUninit`] is preferred over [`ManuallyDrop`],
/// since it helps avoid otherwise scary aliasing problems with `Box<&mut T>`.
///
/// The first step is to "cast" `Box<T>` into `Box<MaybeUninit<T>>` via
/// [`Box::into_raw()`] and [`Box::from_raw()`]. This is then placed into the
/// final storage location using [`DroppingSlot::put()`].
///
/// Then, the returned `&mut Box<MaybeUninit<T>>` is dereferenced twice to
/// obtain an `&mut MaybeUninit<T>`, which [`MaybeUninit::assume_init_mut()`]
/// can convert into an `&mut T`.
///
/// Finally, [`MoveRef::new_unchecked()`] constructs the return value.
///
/// The first step is safe because we construct a `MoveRef` to reinstate the
/// destructor at the end of the function. The second step is safe because
/// we know, a priori, that the `Box` contains an initialized value. The final
/// step is safe, because we know, a priori, that the `Box` owns its pointee.
///
/// ## Worked Example: [`MoveRef<T>`]
///
/// We don't need to inhibit any destructors: we just need to convert a
/// `MoveRef<MoveRef<T>>` into a `MoveRef<T>`, which we can do by using
/// [`MoveRef::into_inner()`]. [`DerefMove::Storage`] can be whatever, so we
/// choose [`()`] for this; the choice is not actually important!
///
/// # Safety
///
/// Implementing `DerefMove` correctly requires that the uniqueness requirement
/// of [`MoveRef`] is upheld. In particular, the following function *must not*
/// violate memory safety:
/// ```
/// # use moveit::{DerefMove, MoveRef, moveit};
/// fn move_out_of<P>(p: P) -> P::Target
/// where
///   P: DerefMove,
///   P::Target: Sized,
/// {
///   unsafe {
///     // Replace `p` with a move reference into it.
///     moveit!(let p = &move *p);
///     
///     // Move out of `p`. From this point on, the `P::Target` destructor must
///     // run when, and only when, the function's return value goes out of
///     // scope per the usual Rust rules.
///     //
///     // In particular, the original `p` or any pointer it came from must not
///     // run the destructor when they go out of scope, under any circumstance.
///     MoveRef::into_inner(p)
///   }
/// }
/// ```
///
/// `deref_move()` must also be `Pin`-safe; even though it does not accept a
/// pinned reference, it must take care to not move its contents at any time.
/// In particular, the implementation of [`PinExt::as_move()`] must be safe by
/// definition.
pub unsafe trait DerefMove: DerefMut + Sized {
  /// The "pure storage" form of `Self`, which owns the storage but not the
  /// pointee.
  type Storage: Sized;

  /// Moves out of `this`, producing a [`MoveRef`] that owns its contents.
  ///
  /// `storage` is a location *somewhere* responsible for rooting the lifetime
  /// of `*this`'s storage. The location is unimportant, so long as it outlives
  /// the resulting [`MoveRef`], which is enforced by the type signature.
  ///
  /// [`moveit!()`] provides a convenient syntax for calling this function.
  fn deref_move<'frame>(
    this: MoveRef<'frame, Self>,
    storage: &'frame mut DroppingSlot<Self::Storage>,
  ) -> MoveRef<'frame, Self::Target>;
}

unsafe impl<'a, T: ?Sized> DerefMove for MoveRef<'a, T> {
  type Storage = ();

  fn deref_move<'frame>(
    this: MoveRef<'frame, Self>,
    _storage: &'frame mut DroppingSlot<Self::Storage>,
  ) -> MoveRef<'frame, Self::Target> {
    MoveRef::into_inner(this)
  }
}

unsafe impl<P> DerefMove for Pin<P>
where
  P: DerefMove,
  P::Target: Unpin,
{
  // SAFETY: We do not need to pin the storage, because `P::Target: Unpin`.
  type Storage = P::Storage;

  fn deref_move<'frame>(
    this: MoveRef<'frame, Self>,
    storage: &'frame mut DroppingSlot<Self::Storage>,
  ) -> MoveRef<'frame, Self::Target> {
    Pin::into_inner(Pin::as_move(this, storage))
  }
}

/// Extensions for using `DerefMove` types with `PinExt`.
pub trait PinExt<P: DerefMove> {
  /// Gets a pinned `MoveRef` out of the pinned pointer.
  ///
  /// This function is best paired with [`moveit!()`]:
  /// ```
  /// # use core::pin::Pin;
  /// # use moveit::{moveit, slot::DroppingSlot, move_ref::PinExt as _};
  /// let ptr = Box::pin(5);
  /// moveit!(let mv = &move ptr);
  /// moveit::slot!(storage);
  /// let mut storage = DroppingSlot::new(storage);
  /// Pin::as_move(mv, &mut storage);
  /// ```
  /// Taking a trip through [`moveit!()`] is unavoidable due to the nature of
  /// `MoveRef`.
  ///
  /// Compare with [`Pin::as_mut()`].
  fn as_move<'frame>(
    this: MoveRef<'frame, Pin<P>>,
    storage: &'frame mut DroppingSlot<P::Storage>,
  ) -> Pin<MoveRef<'frame, P::Target>>;
}

impl<P: DerefMove> PinExt<P> for Pin<P> {
  fn as_move<'frame>(
    this: MoveRef<'frame, Pin<P>>,
    storage: &'frame mut DroppingSlot<P::Storage>,
  ) -> Pin<MoveRef<'frame, P::Target>> {
    unsafe {
      // SAFETY:
      // 1. `Pin<P>` is `repr(transparent)` and can transmute to `P`.
      // 2. `deref_move()` must not move out of the actual storage, merely
      //    shuffle pointers around.
      MoveRef::into_pin(DerefMove::deref_move(this.cast::<P>(), storage))
    }
  }
}

#[doc(hidden)]
pub mod __macro {
  use super::*;
  use core::marker::PhantomData;

  /// Type-inference helper for `moveit!`.
  pub struct DerefPhantom<T>(PhantomData<*const T>);
  impl<T: DerefMove> DerefPhantom<T> {
    #[inline]
    pub fn new(_: &T) -> Self {
      Self(PhantomData)
    }

    #[inline]
    pub fn deref_move<'frame>(
      self,
      this: MoveRef<'frame, T>,
      storage: &'frame mut DroppingSlot<T::Storage>,
    ) -> MoveRef<'frame, T::Target> {
      T::deref_move(this, storage)
    }
  }
}

/// Performs an emplacement operation.
///
/// This macro allows for three exotic types of `let` bindings:
/// ```
/// # use moveit::{moveit, new, move_ref::MoveRef};
/// # use core::pin::Pin;
/// let bx = Box::new(42);
///
/// moveit! {
///   // Use a `New` to construct a new value in place on the stack. This
///   // produces a value of type `Pin<MoveRef<_>>`.
///   let x = new::default::<i32>();
///   
///   // Move out of an existing `DerefMove` type, such as a `Box`. This has
///   // type `MoveRef<_>`, but can be pinned using `MoveRef::into_pin()`.
///   let y = &move *bx;
///   
///   // Create a `MoveRef` of an existing type on the stack. This also has
///   // type `MoveRef<_>`.
///   let z = &move y;
/// }
/// ```
///
/// All three `lets`, including in-place construction, pin to the stack.
/// Consider using something like [`Box::emplace()`] to perform construction on
/// the heap.
///
/// [`Box::emplace()`]: crate::new::Emplace::emplace
#[macro_export]
macro_rules! moveit {
  (let $name:ident $(: $ty:ty)? = &move *$expr:expr $(; $($rest:tt)*)?) => {
    $crate::moveit!(@move $name, $($ty)?, $expr);
    $crate::moveit!($($($rest)*)?);
  };
  (let mut $name:ident $(: $ty:ty)? = &move *$expr:expr $(; $($rest:tt)*)?) => {
    $crate::moveit!(@move(mut) $name, $($ty)?, $expr);
    $crate::moveit!($($($rest)*)?);
  };
  (let $name:ident $(: $ty:ty)? = &move $expr:expr $(; $($rest:tt)*)?) => {
    $crate::moveit!(@put $name, $($ty)?, $expr);
    $crate::moveit!($($($rest)*)?);
  };
  (let mut $name:ident $(: $ty:ty)? = &move $expr:expr $(; $($rest:tt)*)?) => {
    $crate::emplace!(@put(mut) $name, $($ty)?, $expr);
    $crate::emplace!($($($rest)*)?);
  };
  (let $name:ident $(: $ty:ty)? = $expr:expr $(; $($rest:tt)*)?) => {
    $crate::moveit!(@emplace $name, $($ty)?, $expr);
    $crate::moveit!($($($rest)*)?);
  };
  (let mut $name:ident $(: $ty:ty)? = $expr:expr $(; $($rest:tt)*)?) => {
    $crate::moveit!(@emplace(mut) $name, $($ty)?, $expr);
    $crate::moveit!($($($rest)*)?);
  };
  ($(;)?) => {};

  (@move $(($mut:tt))? $name:ident, $($ty:ty)?, $expr:expr) => {
    $crate::slot!(ptr, storage);

    let ptr = ptr.put($expr);
    let mut storage = $crate::slot::DroppingSlot::new(storage);

    #[allow(unused_mut)]
    let $($mut)? $name $(: $ty)? = $crate::move_ref::DerefMove::deref_move(ptr, &mut storage);
  };
  (@put $(($mut:tt))? $name:ident, $($ty:ty)?, $expr:expr) => {
    $crate::slot!(slot);
    let $($mut)? $name $(: $ty)? = slot.put($expr);
  };
  (@emplace $(($mut:tt))? $name:ident, $($ty:ty)?, $expr:expr) => {
    $crate::slot!(slot);
    let $($mut)? $name $(: $ty)? = slot.emplace($expr);
  };
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn deref_move_of_move_ref() {
    moveit! {
      let x = &move Box::new(5);
      let y = &move *x;
    }
    let _ = y;
  }

  #[test]
  fn move_ref_into_inner() {
    moveit!(let x = &move Box::new(5));
    let _ = MoveRef::into_inner(x);
  }
}
