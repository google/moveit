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
//!
//! This module provides a range of helpers such as [`new::by()`] and
//! [`new::from()`] for creating constructors. It is preferred style to
//! `use moveit::new;` and refer to these helpers with a `new::` prefix.

use core::convert::Infallible;
use core::mem::MaybeUninit;
use core::pin::Pin;

#[cfg(doc)]
use {
  crate::new,
  alloc::{boxed::Box, rc::Rc, sync::Arc},
};

mod copy_new;
mod factories;
mod move_new;

pub use copy_new::*;
pub use factories::*;
pub use move_new::*;

/// An in-place constructor for a particular type.
///
/// # Safety
///
/// [`New::new()`] must leave its destination argument in a valid, initialized
/// state.
#[must_use = "`New`s do nothing until emplaced into storage"]
pub unsafe trait New: Sized {
  /// The type to construct.
  type Output;
  /// Construct a new value using the arguments stored in `self`.
  ///
  /// # Safety
  ///
  /// `this` must be freshly-created memory; this function must not
  /// be used to mutate a previously-pinned pointer that has had `self: Pin`
  /// functions called on it.
  unsafe fn new(self, this: Pin<&mut MaybeUninit<Self::Output>>);

  /// Adds a post-construction operation.
  ///
  /// This function wraps `self` in an another [`New`] type which will call
  /// `post` once the main emplacement operation is complete. This is most
  /// useful for the case where creation of the value itself does not depend
  /// on the final address, but where some address-sensitive setup may want
  /// to occur; this can help minimize the scope (or even need for) `unsafe`.
  ///
  /// This function is best combined with other helpers:
  ///
  /// ```
  /// # use moveit::{new, moveit, New};
  /// # use std::pin::Pin;
  /// pub struct MyType { /* ... */ }
  ///
  /// impl MyType {
  ///   pub fn new() -> impl New<Output = Self> {
  ///     new::of(MyType { /* ... */ }).with(|this| {
  ///       // Address-sensitive setup can occur here.
  ///     })
  ///   }
  /// }
  /// ```
  ///
  /// Note: The return value of this function should not be relied upon; a
  /// future version will replace it with `impl New`.
  fn with<F>(self, post: F) -> With<Self, F>
  where
    F: FnOnce(Pin<&mut Self::Output>),
  {
    With(self, post)
  }
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
pub unsafe trait TryNew: Sized {
  /// The type to construct.
  type Output;
  /// The error the construction operation may return.
  type Error;
  /// Try to construct a new value using the arguments stored in `self`.
  ///
  /// # Safety
  ///
  /// `this` must be freshly-created memory; this function must not
  /// be used to mutate a previously-pinned pointer that has had `self: Pin`
  /// functions called on it.
  unsafe fn try_new(
    self,
    this: Pin<&mut MaybeUninit<Self::Output>>,
  ) -> Result<(), Self::Error>;

  /// Adds a post-construction operation.
  ///
  /// This function is analogous to [`New::with()`]; see its documentation for
  /// more information.
  ///
  /// Note: The return value of this function should not be relied upon; a
  /// future version will replace it with `impl TryNew`.
  fn with<F>(self, post: F) -> TryWith<Self, F> {
    TryWith(self, post)
  }
}

unsafe impl<N: New> TryNew for N {
  type Output = N::Output;
  type Error = Infallible;
  unsafe fn try_new(
    self,
    this: Pin<&mut MaybeUninit<Self::Output>>,
  ) -> Result<(), Self::Error> {
    self.new(this);
    Ok(())
  }
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

#[doc(hidden)]
pub struct With<N, F>(N, F);

unsafe impl<N: New, F> New for With<N, F>
where
  F: FnOnce(Pin<&mut N::Output>),
{
  type Output = N::Output;
  #[inline]
  unsafe fn new(self, mut this: Pin<&mut MaybeUninit<Self::Output>>) {
    self.0.new(this.as_mut());
    // Now that `new()` has returned, we can assume `this` is initialized.
    let this = this.map_unchecked_mut(|x| x.assume_init_mut());
    (self.1)(this)
  }
}

#[doc(hidden)]
pub struct TryWith<N, F>(N, F);

unsafe impl<N: TryNew, F> TryNew for TryWith<N, F>
where
  F: FnOnce(Pin<&mut N::Output>) -> Result<(), N::Error>,
{
  type Output = N::Output;
  type Error = N::Error;
  #[inline]
  unsafe fn try_new(
    self,
    mut this: Pin<&mut MaybeUninit<Self::Output>>,
  ) -> Result<(), Self::Error> {
    self.0.try_new(this.as_mut())?;
    // Now that `new()` has returned, we can assume `this` is initialized.
    let this = this.map_unchecked_mut(|x| x.assume_init_mut());
    (self.1)(this)
  }
}
