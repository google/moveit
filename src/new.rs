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

//! In-place constructors.

use core::convert::Infallible;
use core::convert::TryFrom;
use core::convert::TryInto;
use core::marker::PhantomData;
use core::mem;
use core::mem::MaybeUninit;
use core::ops::Deref;
use core::pin::Pin;

use crate::move_ref::DerefMove;
use crate::move_ref::MoveRef;
use crate::move_ref::PinExt as _;

#[cfg(doc)]
use alloc::{boxed::Box, rc::Rc, sync::Arc};

/// An in-place constructor for a particular type.
///
/// # Safety
///
/// [`New::new()`] must leave its destination argument in a valid, initialized
/// state.
#[must_use = "`New`s do nothing until emplaced into storage"]
pub unsafe trait New {
  /// The type to construct.
  type Output;
  /// Construct a new value using the arguments stored in `self`.
  ///
  /// # Safety
  ///
  /// `dest` must be freshly-created memory; this function must not
  /// be used to mutate a previously-pinned pointer that has had `self: Pin`
  /// functions called on it.
  unsafe fn new(self, dest: Pin<&mut MaybeUninit<Self::Output>>);
}

/// Returns a new `New` that uses the provided closure for construction.
///
/// # Safety
///
/// `f` must respect the safety requirements of [`New`], since it is used
/// as an implementation basis.
#[inline]
pub unsafe fn from_placement_fn<T, F>(f: F) -> impl New<Output = T>
where
  F: FnOnce(Pin<&mut MaybeUninit<T>>),
{
  struct FnNew<F, T> {
    f: F,
    _ph: PhantomData<fn(T)>,
  }
  unsafe impl<F, T> New for FnNew<F, T>
  where
    F: FnOnce(Pin<&mut MaybeUninit<T>>),
  {
    type Output = T;
    #[inline]
    unsafe fn new(self, dest: Pin<&mut MaybeUninit<Self::Output>>) {
      (self.f)(dest)
    }
  }

  FnNew::<F, T> {
    f,
    _ph: PhantomData,
  }
}

/// Returns a new `New` that uses the provided closure for constructing a
/// `T`.
///
/// ```
/// # use moveit::{moveit, new};
/// moveit! {
///   let x = new::from_fn(|| 21 * 2);
/// }
/// assert_eq!(*x, 42);
/// ```
#[inline]
pub fn from_fn<T, F>(f: F) -> impl New<Output = T>
where
  F: FnOnce() -> T,
{
  unsafe { from_placement_fn(|mut dest| dest.set(MaybeUninit::new(f()))) }
}

/// Returns a new `New` that uses a `From` implementation to generate a `T`.
///
/// ```
/// # use std::pin::Pin;
/// # use moveit::{moveit, new, MoveRef};
/// moveit! {
///   let x: Pin<MoveRef<String>> = new::from("foo");
/// }
/// assert_eq!(*x, "foo");
/// ```
#[inline]
pub fn from<T: From<U>, U>(val: U) -> impl New<Output = T> {
  from_fn(|| val.into())
}

/// Returns a new `New` that simply returns the given value.
///
/// ```
/// # use std::pin::Pin;
/// # use moveit::{moveit, new};
/// moveit! {
///   let x = new::new(42);
/// }
/// assert_eq!(*x, 42);
/// ```
#[inline]
pub fn new<T>(val: T) -> impl New<Output = T> {
  from_fn(|| val)
}

/// Returns a new `New` that uses a `Default` implementation to generate a `T`.
///
/// ```
/// # use std::pin::Pin;
/// # use moveit::{moveit, new};
/// moveit! {
///   let x = new::default::<i32>();
/// }
/// assert_eq!(*x, 0);
/// ```
#[inline]
pub fn default<T: Default>() -> impl New<Output = T> {
  from_fn(Default::default)
}

/// An in-place constructor for a particular type, which can potentially fail.
///
/// Emplacing a `TryNew` may allocate even when construction fails; prefer to
/// use `Result<impl New>` when possible, instead.
///
/// # Safety
///
/// [`TryNew::try_new()`] must leave its destination argument in a valid,
/// initialized state when it returns `Ok`.
#[must_use = "`New`s do nothing until emplaced into storage"]
pub unsafe trait TryNew {
  /// The type to construct.
  type Output;
  /// The error the construction operation may return.
  type Error;
  /// Try to construct a new value using the arguments stored in `self`.
  ///
  /// # Safety
  ///
  /// `dest` must be freshly-created memory; this function must not
  /// be used to mutate a previously-pinned pointer that has had `self: Pin`
  /// functions called on it.
  unsafe fn try_new(
    self,
    dest: Pin<&mut MaybeUninit<Self::Output>>,
  ) -> Result<(), Self::Error>;
}

unsafe impl<N: New> TryNew for N {
  type Output = N::Output;
  type Error = Infallible;
  unsafe fn try_new(
    self,
    dest: Pin<&mut MaybeUninit<Self::Output>>,
  ) -> Result<(), Self::Error> {
    self.new(dest);
    Ok(())
  }
}

/// Returns a new `TryNew` that uses the provided closure for construction.
///
/// # Safety
///
/// `f` must respect the safety requirements of [`TryNew`], since it is used
/// as an implementation basis.
#[inline]
pub unsafe fn from_placement_try_fn<T, E, F>(
  f: F,
) -> impl TryNew<Output = T, Error = E>
where
  F: FnOnce(Pin<&mut MaybeUninit<T>>) -> Result<(), E>,
{
  struct FnNew<F, T, E> {
    f: F,
    _ph: PhantomData<fn(T) -> E>,
  }
  unsafe impl<F, T, E> TryNew for FnNew<F, T, E>
  where
    F: FnOnce(Pin<&mut MaybeUninit<T>>) -> Result<(), E>,
  {
    type Output = T;
    type Error = E;
    #[inline]
    unsafe fn try_new(
      self,
      dest: Pin<&mut MaybeUninit<Self::Output>>,
    ) -> Result<(), E> {
      (self.f)(dest)
    }
  }

  FnNew::<F, T, E> {
    f,
    _ph: PhantomData,
  }
}

/// Returns a new `New` that uses the provided closure for constructing a
/// `T`.
#[inline]
pub fn from_try_fn<T, E, F>(f: F) -> impl TryNew<Output = T, Error = E>
where
  F: FnOnce() -> Result<T, E>,
{
  unsafe {
    from_placement_try_fn(|mut dest| Ok(dest.set(MaybeUninit::new(f()?))))
  }
}

/// Returns a new `New` that uses a `From` implementation to generate a `T`.
#[inline]
pub fn try_from<T: TryFrom<U>, U>(
  val: U,
) -> impl TryNew<Output = T, Error = T::Error> {
  from_try_fn(|| val.try_into())
}

/// A pointer type with a stable address that a [`New`] may be used to
/// construct a value with.
///
/// This enables an `emplace()` method for [`Box`], [`Rc`], and [`Arc`]. Users
/// are encouraged to implement this function for their own heap-allocated smart
/// pointers.
pub trait Emplace<T>: Sized {
  /// Constructs a new smart pointer and emplaces `n` into its storage.
  fn emplace<N: New<Output = T>>(n: N) -> Pin<Self> {
    match Self::try_emplace(n) {
      Ok(x) => x,
      Err(e) => match e {},
    }
  }

  /// Constructs a new smart pointer and tries to emplace `n` into its storage.
  fn try_emplace<N: TryNew<Output = T>>(n: N) -> Result<Pin<Self>, N::Error>;
}

/// A move constructible type: a destination-aware `Clone` that destroys the
/// moved-from value.
///
/// # Safety
///
/// After [`MoveNew::move_new()`] is called:
/// - `src` should be treated as having been destroyed.
/// - `dest` must have been initialized.
pub unsafe trait MoveNew: Sized {
  /// Move-construct `src` into `dest`, effectively re-pinning it at a new
  /// location.
  ///
  /// # Safety
  ///
  /// The same safety requirements of [`New::new()`] apply, but, in addition,
  /// `*src` must not be used after this function is called, because it has
  /// effectively been destroyed.
  unsafe fn move_new(
    src: Pin<MoveRef<Self>>,
    dest: Pin<&mut MaybeUninit<Self>>,
  );
}

/// Returns a new `New` that uses a move constructor.
#[inline]
pub fn mov<P>(ptr: impl Into<Pin<P>>) -> impl New<Output = P::Target>
where
  P: DerefMove,
  P::Target: MoveNew,
{
  let ptr = ptr.into();
  unsafe {
    from_placement_fn(move |dest| {
      crate::moveit!(let ptr = &move ptr);
      MoveNew::move_new(Pin::as_move(ptr), dest);
    })
  }
}

/// A copy constructible type: a destination-aware `Clone`.
///
/// # Safety
///
/// After [`CopyNew::copy_new()`] is called:
/// - `dest` must have been initialized.
pub unsafe trait CopyNew: Sized {
  /// Copy-construct `src` into `dest`, effectively re-pinning it at a new
  /// location.
  ///
  /// # Safety
  ///
  /// The same safety requirements of [`New::new()`] apply.
  unsafe fn copy_new(src: &Self, dest: Pin<&mut MaybeUninit<Self>>);
}

/// Returns a new `New` that uses a copy constructor.
#[inline]
pub fn copy<P>(ptr: P) -> impl New<Output = P::Target>
where
  P: Deref,
  P::Target: CopyNew,
{
  unsafe {
    from_placement_fn(move |dest| {
      CopyNew::copy_new(&*ptr, dest);

      // Because `*ptr` is still intact, we can drop it normally.
      mem::drop(ptr)
    })
  }
}
