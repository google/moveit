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

//! Explicit stack slots, which can be used for stack emplacement.
//!
//! A [`Slot`] is uninitialized storage on the stack that can be manipulated
//! explicitly. Notionally, a [`Slot<T>`] represents a `let x: T;` in some
//! function's stack.
//!
//! [`Slot`]s mut be created with the [`slot!()`] macro:
//! ```
//! # use moveit::{slot};
//! slot!(storage);
//! let mut x = storage.put(42);
//! *x /= 2;
//! assert_eq!(*x, 21);
//! ```
//! Unfortunately, due to the constrains of Rust today, it is not possible to
//! produce a [`Slot`] as part of a larger expression; since it needs to expand
//! to a `let` to bind the stack location, [`slot!()`] must be a statement, not
//! an expression.
//!
//! [`Slot`]s can also be used to implement a sort of "guaranteed RVO":
//! ```
//! # use moveit::{slot, Slot, move_ref::MoveRef};
//! fn returns_on_the_stack(val: i32, storage: Slot<i32>) -> Option<MoveRef<i32>> {
//!   if val == 0 {
//!     return None
//!   }
//!   Some(storage.put(val))
//! }
//!
//! slot!(storage);
//! let val = returns_on_the_stack(42, storage);
//! assert_eq!(*val.unwrap(), 42);
//! ```
//!
//! [`Slot`]s provide a natural location for emplacing values on the stack.
//! The [`moveit!()`] macro is intended to make this operation
//! straight-forward.
//!
//! # [`DroppingSlot`]
//!
//! [`DroppingSlot`] is a support type similar to [`Slot`] that is used for
//! implementing [`DerefMove`], but which users should otherwise not construct
//! themselves (despite it being otherwise perfectly safe to do so).

use core::mem;
use core::mem::MaybeUninit;
use core::pin::Pin;
use core::ptr;

use crate::move_ref::MoveRef;
use crate::new;
use crate::new::New;
use crate::new::TryNew;

#[cfg(doc)]
use {crate::move_ref::DerefMove, alloc::boxed::Box};

/// An empty slot on the stack into which a value could be emplaced.
///
/// The `'frame` lifetime refers to the lifetime of the stack frame this
/// `Slot`'s storage is allocated on.
///
/// See [`slot!()`] and [the module documentation][self].
pub struct Slot<'frame, T>(&'frame mut MaybeUninit<T>);

impl<'frame, T> Slot<'frame, T> {
  /// Creates a new `Slot` with the given pointer as its basis.
  ///
  /// To safely construct a `Slot`, use [`slot!()`].
  ///
  /// # Safety
  /// `ptr` must not be outlived by any other pointers to its allocation.
  pub unsafe fn new_unchecked(ptr: &'frame mut MaybeUninit<T>) -> Self {
    Self(ptr)
  }

  /// Put `val` into this slot, returning a new [`MoveRef`].
  pub fn put(self, val: T) -> MoveRef<'frame, T> {
    unsafe {
      // SAFETY: Pinning is conserved by this operation.
      Pin::into_inner_unchecked(self.pin(val))
    }
  }

  /// Pin `val` into this slot, returning a new, pinned [`MoveRef`].
  pub fn pin(self, val: T) -> Pin<MoveRef<'frame, T>> {
    self.emplace(new::of(val))
  }

  /// Emplace `new` into this slot, returning a new, pinned [`MoveRef`].
  pub fn emplace<N: New<Output = T>>(self, new: N) -> Pin<MoveRef<'frame, T>> {
    match self.try_emplace(new) {
      Ok(x) => x,
      Err(e) => match e {},
    }
  }

  /// Try to emplace `new` into this slot, returning a new, pinned [`MoveRef`].
  pub fn try_emplace<N: TryNew<Output = T>>(
    self,
    new: N,
  ) -> Result<Pin<MoveRef<'frame, T>>, N::Error> {
    unsafe {
      new.try_new(Pin::new_unchecked(self.0))?;
      Ok(MoveRef::into_pin(MoveRef::new_unchecked(
        self.0.assume_init_mut(),
      )))
    }
  }

  /// Converts this into a slot for a pinned `T`.
  ///
  /// This is safe, since this `Slot` owns the referenced data, and
  /// `Pin` is explicitly a `repr(transparent)` type.
  pub fn into_pinned(self) -> Slot<'frame, Pin<T>> {
    unsafe { self.cast() }
  }

  /// Converts this `Slot` from being a slot for a `T` to being a slot for
  /// some other type `U`.
  ///
  /// ```
  /// # use moveit::{Slot, MoveRef};
  /// moveit::slot!(place: u32);
  /// let foo: MoveRef<u16> = unsafe { place.cast::<u16>() }.put(42);
  /// ```
  ///
  /// # Safety
  ///
  /// `T` must have at least the size and alignment as `U`.
  pub unsafe fn cast<U>(self) -> Slot<'frame, U> {
    debug_assert!(mem::size_of::<T>() >= mem::size_of::<U>());
    debug_assert!(mem::align_of::<T>() >= mem::align_of::<U>());
    Slot(&mut *(self.0 as *mut MaybeUninit<T> as *mut MaybeUninit<U>))
  }
}

impl<'frame, T> Slot<'frame, Pin<T>> {
  /// Converts this into a slot for an unpinned `T`.
  ///
  /// This is safe, since this `Slot` owns the referenced data, and
  /// `Pin` is explicitly a `repr(transparent)` type.
  ///
  /// Moreover, no actual unpinning is occurring: the referenced data must
  /// be uninitialized, so it cannot have a pinned referent.
  pub fn into_unpinned(self) -> Slot<'frame, T> {
    unsafe { self.cast() }
  }
}

/// Similar to a [`Slot`], but able to drop its contents.
///
/// A `DroppingSlot` wraps a `Slot`, but includes a *drop_flag*. `DroppingSlot`s
/// are entitled to drop the contents of the wrapped `Slot` *if a value has been
/// placed into it*.
///
/// `DroppingSlot` exposes an API surface similar to `Slot`'s, but with a key
/// difference: all functions take `&mut self`, and return `&mut T`. The
/// contents of the `DroppingSlot` are only accessible *once*: the first time
/// that `emplace()` or a similar function is called. Because these functions
/// take `&mut self`, they will all panic if called after the slot is filled.
///
/// In general, users of `moveit` should not be constructing `DroppingSlot`;
/// instead, the [`moveit!()`] machinery constructs them and passes them into
/// [`DerefMove::deref_move()`], which is where users will primarily encounter
/// it.
pub struct DroppingSlot<'frame, T> {
  filled: bool,
  slot: Slot<'frame, T>,
}

impl<'frame, T> DroppingSlot<'frame, T> {
  /// Creates a new `OwningSlot` that wraps `slot`.
  pub fn new(slot: Slot<'frame, T>) -> Self {
    Self {
      filled: false,
      slot,
    }
  }

  /// Put `val` into this slot, returning a reference to it.
  ///
  /// # Panics
  ///
  /// Panics if called after the slot has been filled.
  pub fn put(&mut self, val: T) -> &mut T {
    unsafe {
      // SAFETY: Pinning is conserved by this operation.
      Pin::into_inner_unchecked(self.pin(val))
    }
  }

  /// Pin `val` into this slot, returning a new, pinned reference to it.
  ///
  /// # Panics
  ///
  /// Panics if called after the slot has been filled.
  pub fn pin(&mut self, val: T) -> Pin<&mut T> {
    self.emplace(new::of(val))
  }

  /// Emplace `new` into this slot, returning a new, pinned reference to it.
  ///
  /// # Panics
  ///
  /// Panics if called after the slot has been filled.
  pub fn emplace<N: New<Output = T>>(&mut self, new: N) -> Pin<&mut T> {
    match self.try_emplace(new) {
      Ok(x) => x,
      Err(e) => match e {},
    }
  }

  /// Try to emplace `new` into this slot, returning a new, pinned reference to
  /// it.
  ///
  /// If this function returns `Err`, the slot is *not* filled.
  ///
  /// # Panics
  ///
  /// Panics if called after the slot has been filled.
  pub fn try_emplace<N: TryNew<Output = T>>(
    &mut self,
    new: N,
  ) -> Result<Pin<&mut T>, N::Error> {
    assert!(!self.filled);
    unsafe {
      new.try_new(Pin::new_unchecked(self.slot.0))?;
      self.filled = true;
      Ok(Pin::new_unchecked(self.slot.0.assume_init_mut()))
    }
  }
}

impl<T> Drop for DroppingSlot<'_, T> {
  fn drop(&mut self) {
    if self.filled {
      unsafe { ptr::drop_in_place(self.slot.0 as *mut _ as *mut T) }
    }
  }
}

#[doc(hidden)]
pub mod __macro {
  pub use core;
}

/// Constructs a new [`Slot`].
///
/// Because [`Slot`]s need to own data on the stack, but that data cannot
/// move with the [`Slot`], it must be constructed using this macro. For
/// example:
/// ```
/// moveit::slot!(x, y: bool);
/// let x = x.put(5);
/// let y = y.put(false);
/// ```
///
/// This macro is especially useful for passing data into functions that want to
/// emplace a value into the caller.
#[macro_export]
macro_rules! slot {
  ($($name:ident $(: $ty:ty)?),* $(,)*) => {$(
    let mut uninit = $crate::slot::__macro::core::mem::MaybeUninit::<
      $crate::slot!(@tyof $($ty)?)
    >::uninit();
    #[allow(unsafe_code, unused_unsafe)]
    let $name = unsafe { $crate::slot::Slot::new_unchecked(&mut uninit) };
  )*};
  (@tyof) => {_};
  (@tyof $ty:ty) => {$ty};
}
