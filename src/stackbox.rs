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

//! Stack-based owning pointers, for emplacement on the stack.
//!
//! A [`StackBox`] can be created using the [`stackbox!()`] macro:
//! ```
//! # use moveit::stackbox;
//! stackbox!(let mut x = 5);
//! *x += 1;
//! assert_eq!(*x, 6);
//! ```
//! Because a [`StackBox`] truly owns its contents, it will destroy them once it
//! goes out of scope. However, a [`StackBox`] cannot escape the scope it is
//! created in, since its storage is destroyed once that stack frame ends.
//! Thus, [`StackBox`]es cannot be returned directly.
//!
//! A [`Slot`] is uninitialized storage for a [`StackBox`], which can be
//! consumed to produce a [`StackBox`]. [`Slot`]s mut be created with the
//! [`slot!()`] macro:
//! ```
//! # use moveit::{slot, StackBox};
//! slot!(storage);
//! let mut x = StackBox::new(42, storage);
//! *x /= 2;
//! assert_eq!(*x, 21);
//! ```
//!
//! [`Slot`]s can also be used to implement a sort of "guaranteed RVO":
//! ```
//! # use moveit::{slot, Slot, StackBox};
//! fn returns_on_the_stack(val: i32, storage: Slot<i32>) -> Option<StackBox<i32>> {
//!   if val == 0 {
//!     return None
//!   }
//!   Some(StackBox::new(val, storage))
//! }
//!
//! slot!(storage);
//! let val = returns_on_the_stack(42, storage);
//! assert_eq!(*val.unwrap(), 42);
//! ```
//!
//! Because they are pointer-like but uniquely own their contents, [`Ctor`]s
//! can be emplaced on the stack using [`StackBox`], but way of [`StackBox::emplace()`]
//! or the [`emplace!()`] macro.

use core::mem;
use core::mem::MaybeUninit;
use core::ops::Deref;
use core::ops::DerefMut;
use core::pin::Pin;
use core::ptr;

use crate::ctor;
use crate::ctor::Ctor;
use crate::ctor::TryCtor;
use crate::unique::DerefMove;
use crate::unique::OuterDrop;

#[cfg(doc)]
use alloc::boxed::Box;

/// An empty slot on the stack into which a value could be emplaced.
///
/// The `'frame` lifetime refers to the lifetime of the stack frame this
/// `Slot`'s storage is allocated on.
///
/// See [`slot!()`].
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

  /// Put `val` into this slot, returning a new [`StackBox`].
  ///
  /// The [`stackbox!()`] macro is a shorthand for this function.
  pub fn put(self, val: T) -> StackBox<'frame, T> {
    *self.0 = MaybeUninit::new(val);
    unsafe { StackBox::new_unchecked(&mut *(self.0 as *mut _ as *mut T)) }
  }

  /// Pin `val` into this slot, returning a new, pinned [`StackBox`].
  pub fn pin(self, val: T) -> Pin<StackBox<'frame, T>> {
    self.emplace(ctor::new(val))
  }

  /// Emplace `ctor` into this slot, returning a new, pinned [`StackBox`].
  ///
  /// The [`emplace!()`] macro is a shorthand for this function.
  pub fn emplace<C: Ctor<Output = T>>(
    self,
    ctor: C,
  ) -> Pin<StackBox<'frame, T>> {
    unsafe {
      ctor.ctor(Pin::new_unchecked(self.0));
      Pin::new_unchecked(StackBox::new_unchecked(
        &mut *(self.0 as *mut _ as *mut T),
      ))
    }
  }

  /// Try to emplace `ctor` into this slot, returning a new, pinned [`StackBox`].
  pub fn try_emplace<C: TryCtor<Output = T>>(
    self,
    ctor: C,
  ) -> Result<Pin<StackBox<'frame, T>>, C::Error> {
    unsafe {
      ctor.try_ctor(Pin::new_unchecked(self.0))?;
      Ok(Pin::new_unchecked(StackBox::new_unchecked(
        &mut *(self.0 as *mut _ as *mut T),
      )))
    }
  }
}

/// A stack-based owning pointer.
///
/// The `'frame` lifetime refers to the lifetime of the stack frame this
/// `StackBox`'s storage is allocated on.
///
/// This type is useful for when emplacement and move constructors are desired
/// but no allocator is available.
pub struct StackBox<'frame, T>(&'frame mut T);

impl<'frame, T> StackBox<'frame, T> {
  /// Alternate spelling for [`Slot::put()`].
  pub fn new(val: T, slot: Slot<'frame, T>) -> Self {
    slot.put(val)
  }

  /// Alternate spelling for [`Slot::pin()`].
  pub fn pin(val: T, slot: Slot<'frame, T>) -> Pin<Self> {
    slot.pin(val)
  }

  /// Alternate spelling for [`Slot::emplace()`].
  pub fn emplace<C: Ctor<Output = T>>(
    ctor: C,
    slot: Slot<'frame, T>,
  ) -> Pin<Self> {
    slot.emplace(ctor)
  }

  /// Alternate spelling for [`Slot::try_emplace()`].
  pub fn try_emplace<C: TryCtor<Output = T>>(
    ctor: C,
    slot: Slot<'frame, T>,
  ) -> Result<Pin<Self>, C::Error> {
    slot.try_emplace(ctor)
  }

  /// Creates a new `StackBox` with the given pointer as its basis.
  ///
  /// To safely construct a `StackBox`, use [`emplace!()`] or [`stackbox!()`].
  ///
  /// # Safety
  /// `ptr` must not be outlived by any other pointers to its allocation.
  pub unsafe fn new_unchecked(ptr: &'frame mut T) -> Self {
    Self(ptr)
  }

  /// Consumes this `StackBox`, returning the contents inside.
  pub fn into_inner(this: Self) -> T {
    let val = unsafe { (this.0 as *mut T).read() };
    mem::forget(this);
    val
  }

  /// Consumes this `StackBox`, returning the stack-bound reference inside.
  ///
  /// This function is analogous to [`Box::leak()`]; it is the caller's
  /// responsibility to call `T`'s destructor.
  pub fn leak(this: Self) -> &'frame mut T {
    let val = this.0 as *mut T;
    mem::forget(this);
    unsafe { &mut *val }
  }
}

impl<T> Drop for StackBox<'_, T> {
  fn drop(&mut self) {
    unsafe { ptr::drop_in_place(self.0) }
  }
}

impl<T> Deref for StackBox<'_, T> {
  type Target = T;
  fn deref(&self) -> &T {
    &*self.0
  }
}

impl<T> DerefMut for StackBox<'_, T> {
  fn deref_mut(&mut self) -> &mut T {
    &mut *self.0
  }
}

unsafe impl<T> OuterDrop for StackBox<'_, T> {
  unsafe fn outer_drop(_: *mut Self) {
    // Stack storage is automatically destroyed for us.
  }
}

unsafe impl<T> DerefMove for StackBox<'_, T> {}

#[doc(hidden)]
pub mod __macro {
  pub use core;
}

/// Emplace a [`Ctor`] into a [`StackBox`].
///
/// This macro is analogous to the [`stackbox!`] macro, except that the RHS must
/// be a `Ctor<Output = T>` instead of a `T`, and the resulting type is a
/// `Pin<StackBox<T>>`.
/// ```
/// # use moveit::{emplace, ctor, StackBox};
/// # use core::pin::Pin;
/// emplace!(let x = ctor::default::<i32>());
/// emplace! {
///   let y: Pin<StackBox<i32>> = ctor::from(*x);
///   let mut z = ctor::new(*y as u64);
/// }
/// # let _ = z;
/// ```
///
/// This macro is a shortcut for calling [`slot!()`] followed by
/// [`Slot::emplace()`].
#[macro_export]
#[cfg(doc)]
macro_rules! emplace {
  ($(let $(mut)? $name:ident $(: $ty:ty)? = $expr:expr);*) => { ... }
}

/// Shh...
#[macro_export]
#[cfg(not(doc))]
macro_rules! emplace {
  (let $name:ident $(: $ty:ty)? = $expr:expr $(; $($rest:tt)*)?) => {
    $crate::emplace!(@emplace $name, $($ty)?, $expr);
    $crate::emplace!($($($rest)*)?);
  };
  (let mut $name:ident $(: $ty:ty)? = $expr:expr $(; $($rest:tt)*)?) => {
    $crate::emplace!(@emplace(mut) $name, $($ty)?, $expr);
    $crate::emplace!($($($rest)*)?);
  };
  ($(;)?) => {};

  (@emplace $(($mut:tt))? $name:ident, $($ty:ty)?, $expr:expr) => {
    $crate::slot!($name);
    let $($mut)? $name $(: $ty)? = $name.emplace($expr);
  };
}

/// Constructs a [`StackBox`].
///
/// Because [`StackBox`]es need to own data on the stack, but that data cannot
/// move with the [`StackBox`], it must be constructed using this macro. For
/// example:
/// ```
/// # use moveit::{stackbox, StackBox};
/// stackbox!(let x = 5);
/// stackbox! {
///   let y: StackBox<i32> = StackBox::into_inner(x);
///   let mut z = *y as u64;
/// }
/// # let _ = z;
/// ```
///
/// This macro is a shortcut for calling [`slot!()`] followed by
/// [`Slot::put()`].
#[macro_export]
#[cfg(doc)]
macro_rules! stackbox {
  ($(let $(mut)? $name:ident $(: $ty:ty)? = $expr:expr);*) => { ... }
}

/// Shh...
#[macro_export]
#[cfg(not(doc))]
macro_rules! stackbox {
  (let $name:ident $(: $ty:ty)? = $expr:expr $(; $($rest:tt)*)?) => {
    $crate::stackbox!(@emplace $name, $($ty)?, $expr);
    $crate::stackbox!($($($rest)*)?);
  };
  (let mut $name:ident $(: $ty:ty)? = $expr:expr $(; $($rest:tt)*)?) => {
    $crate::stackbox!(@emplace(mut) $name, $($ty)?, $expr);
    $crate::stackbox!($($($rest)*)?);
  };
  ($(;)?) => {};

  (@emplace $(($mut:tt))? $name:ident, $($ty:ty)?, $expr:expr) => {
    $crate::slot!($name);
    let $($mut)? $name $(: $ty)? = $name.put($expr);
  };
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
#[cfg(doc)]
macro_rules! slot {
  ($($name:ident $(: $ty:ty)?),*) => { ... }
}

/// Shh...
#[macro_export]
#[cfg(not(doc))]
macro_rules! slot {
  ($($name:ident $(: $ty:ty)?),* $(,)*) => {$(
    let mut uninit = $crate::stackbox::__macro::core::mem::MaybeUninit::<$crate::slot!(@tyof $($ty)?)>::uninit();
    let $name = unsafe {
      $crate::stackbox::Slot::new_unchecked(&mut uninit)
    };
  )*};
  (@tyof) => {_};
  (@tyof $ty:ty) => {$ty};
}
