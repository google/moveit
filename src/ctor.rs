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
/// [`Ctor::ctor()`] must leave its destination argument in a valid, initialized
/// state.
#[must_use = "`Ctor`s do nothing until emplaced into storage"]
pub unsafe trait Ctor {
  /// The type to construct.
  type Output;
  /// Construct a new value using the arguments stored in `self`.
  ///
  /// # Safety
  ///
  /// `dest` must be freshly-created memory; this function must not
  /// be used to mutate a previously-pinned pointer that has had `self: Pin`
  /// functions called on it.
  unsafe fn ctor(self, dest: Pin<&mut MaybeUninit<Self::Output>>);
}

/// Returns a new `Ctor` that uses the provided closure for construction.
///
/// # Safety
///
/// `f` must respect the safety requirements of [`Ctor`], since it is used
/// as an implementation basis.
#[inline]
pub unsafe fn from_placement_fn<T, F>(f: F) -> impl Ctor<Output = T>
where
  F: FnOnce(Pin<&mut MaybeUninit<T>>),
{
  struct FnCtor<F, T> {
    f: F,
    _ph: PhantomData<fn(T)>,
  }
  unsafe impl<F, T> Ctor for FnCtor<F, T>
  where
    F: FnOnce(Pin<&mut MaybeUninit<T>>),
  {
    type Output = T;
    #[inline]
    unsafe fn ctor(self, dest: Pin<&mut MaybeUninit<Self::Output>>) {
      (self.f)(dest)
    }
  }

  FnCtor::<F, T> {
    f,
    _ph: PhantomData,
  }
}

/// Returns a new `Ctor` that uses the provided closure for constructing a
/// `T`.
///
/// ```
/// # use moveit::{emplace, ctor};
/// emplace! {
///   let x = ctor::from_fn(|| 21 * 2);
/// }
/// assert_eq!(*x, 42);
/// ```
#[inline]
pub fn from_fn<T, F>(f: F) -> impl Ctor<Output = T>
where
  F: FnOnce() -> T,
{
  unsafe { from_placement_fn(|mut dest| dest.set(MaybeUninit::new(f()))) }
}

/// Returns a new `Ctor` that uses a `From` implementation to generate a `T`.
///
/// ```
/// # use std::pin::Pin;
/// # use moveit::{emplace, ctor, StackBox};
/// emplace! {
///   let x: Pin<StackBox<String>> = ctor::from("foo");
/// }
/// assert_eq!(*x, "foo");
/// ```
#[inline]
pub fn from<T: From<U>, U>(val: U) -> impl Ctor<Output = T> {
  from_fn(|| val.into())
}

/// Returns a new `Ctor` that simply returns the given value.
///
/// ```
/// # use std::pin::Pin;
/// # use moveit::{emplace, ctor, StackBox};
/// emplace! {
///   let x = ctor::new(42);
/// }
/// assert_eq!(*x, 42);
/// ```
#[inline]
pub fn new<T>(val: T) -> impl Ctor<Output = T> {
  from_fn(|| val)
}

/// Returns a new `Ctor` that uses a `Default` implementation to generate a `T`.
///
/// ```
/// # use std::pin::Pin;
/// # use moveit::{emplace, ctor, StackBox};
/// emplace! {
///   let x = ctor::default::<i32>();
/// }
/// assert_eq!(*x, 0);
/// ```
#[inline]
pub fn default<T: Default>() -> impl Ctor<Output = T> {
  from_fn(Default::default)
}

/// An in-place constructor for a particular type, which can potentially fail.
///
/// Emplacing a `TryCtor` may allocate even when construction fails; prefer to
/// use `Result<impl Ctor>` when possible, instead.
///
/// # Safety
///
/// [`TryCtor::try_ctor()`] must leave its destination argument in a valid,
/// initialized state when it returns `Ok`.
#[must_use = "`Ctor`s do nothing until emplaced into storage"]
pub unsafe trait TryCtor {
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
  unsafe fn try_ctor(
    self,
    dest: Pin<&mut MaybeUninit<Self::Output>>,
  ) -> Result<(), Self::Error>;
}

unsafe impl<C: Ctor> TryCtor for C {
  type Output = C::Output;
  type Error = Infallible;
  unsafe fn try_ctor(
    self,
    dest: Pin<&mut MaybeUninit<Self::Output>>,
  ) -> Result<(), Self::Error> {
    self.ctor(dest);
    Ok(())
  }
}

/// Returns a new `TryCtor` that uses the provided closure for construction.
///
/// # Safety
///
/// `f` must respect the safety requirements of [`TryCtor`], since it is used
/// as an implementation basis.
#[inline]
pub unsafe fn from_placement_try_fn<T, E, F>(
  f: F,
) -> impl TryCtor<Output = T, Error = E>
where
  F: FnOnce(Pin<&mut MaybeUninit<T>>) -> Result<(), E>,
{
  struct FnCtor<F, T, E> {
    f: F,
    _ph: PhantomData<fn(T) -> E>,
  }
  unsafe impl<F, T, E> TryCtor for FnCtor<F, T, E>
  where
    F: FnOnce(Pin<&mut MaybeUninit<T>>) -> Result<(), E>,
  {
    type Output = T;
    type Error = E;
    #[inline]
    unsafe fn try_ctor(
      self,
      dest: Pin<&mut MaybeUninit<Self::Output>>,
    ) -> Result<(), E> {
      (self.f)(dest)
    }
  }

  FnCtor::<F, T, E> {
    f,
    _ph: PhantomData,
  }
}

/// Returns a new `Ctor` that uses the provided closure for constructing a
/// `T`.
#[inline]
pub fn from_try_fn<T, E, F>(f: F) -> impl TryCtor<Output = T, Error = E>
where
  F: FnOnce() -> Result<T, E>,
{
  unsafe {
    from_placement_try_fn(|mut dest| Ok(dest.set(MaybeUninit::new(f()?))))
  }
}

/// Returns a new `Ctor` that uses a `From` implementation to generate a `T`.
#[inline]
pub fn try_from<T: TryFrom<U>, U>(
  val: U,
) -> impl TryCtor<Output = T, Error = T::Error> {
  from_try_fn(|| val.try_into())
}

/// A pointer type with a stable address that a [`Ctor`] may be used to
/// construct a value with.
///
/// This enables an `emplace()` method for [`Box`], [`Rc`], and [`Arc`]. Users
/// are encouraged to implement this function for their own heap-allocated smart
/// pointers.
pub trait Emplace<T>: Sized {
  /// Constructs a new smart pointer and emplaces `c` into its storage.
  fn emplace<C: Ctor<Output = T>>(c: C) -> Pin<Self> {
    match Self::try_emplace(c) {
      Ok(x) => x,
      Err(e) => match e {},
    }
  }

  /// Constructs a new smart pointer and tries to emplace `c` into its storage.
  fn try_emplace<C: TryCtor<Output = T>>(c: C) -> Result<Pin<Self>, C::Error>;
}

/// A move constructible type: a destination-aware `Clone` that destroys the
/// moved-from value.
///
/// # Safety
///
/// After [`MoveCtor::move_ctor()`] is called:
/// - `src` should be treated as having been destroyed.
/// - `dest` must have been initialized.
pub unsafe trait MoveCtor: Sized {
  /// Move-construct `src` into `dest`, effectively re-pinning it at a new
  /// location.
  ///
  /// # Safety
  ///
  /// The same safety requirements of [`Ctor::ctor()`] apply, but, in addition,
  /// `*src` must not be used after this function is called, because it has
  /// effectively been destroyed.
  unsafe fn move_ctor(
    src: Pin<MoveRef<Self>>,
    dest: Pin<&mut MaybeUninit<Self>>,
  );
}

/// Returns a new `Ctor` that uses a move constructor.
#[inline]
pub fn mov<P>(ptr: impl Into<Pin<P>>) -> impl Ctor<Output = P::Target>
where
  P: DerefMove,
  P::Target: MoveCtor,
{
  let ptr = ptr.into();
  unsafe {
    from_placement_fn(move |dest| {
      crate::moveit!(let ptr = &move ptr);
      MoveCtor::move_ctor(Pin::as_move(ptr), dest);
    })
  }
}

/// A copy constructible type: a destination-aware `Clone`.
///
/// # Safety
///
/// After [`CopyCtor::copy_ctor()`] is called:
/// - `dest` must have been initialized.
pub unsafe trait CopyCtor: Sized {
  /// Copy-construct `src` into `dest`, effectively re-pinning it at a new
  /// location.
  ///
  /// # Safety
  ///
  /// The same safety requirements of [`Ctor::ctor()`] apply.
  unsafe fn copy_ctor(src: &Self, dest: Pin<&mut MaybeUninit<Self>>);
}

/// Returns a new `Ctor` that uses a copy constructor.
#[inline]
pub fn copy<P>(ptr: P) -> impl Ctor<Output = P::Target>
where
  P: Deref,
  P::Target: CopyCtor,
{
  unsafe {
    from_placement_fn(move |dest| {
      CopyCtor::copy_ctor(&*ptr, dest);

      // Because `*ptr` is still intact, we can drop it normally.
      mem::drop(ptr)
    })
  }
}
