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
use core::mem::MaybeUninit;
use core::pin::Pin;

#[cfg(doc)]
use alloc::{boxed::Box, rc::Rc, sync::Arc};

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
