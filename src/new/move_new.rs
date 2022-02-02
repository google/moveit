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

use core::mem::MaybeUninit;
use core::pin::Pin;
use core::ops::Deref;

use crate::move_ref::DerefMove;
use crate::move_ref::MoveRef;
use crate::move_ref::PinExt as _;
use crate::new;
use crate::new::New;
use crate::slot;
use crate::slot::DroppingSlot;

/// A move constructible type: a destination-aware `Clone` that destroys the
/// moved-from value.
///
/// # Safety
///
/// After [`MoveNew::move_new()`] is called:
/// - `src` should be treated as having been destroyed.
/// - `this` must have been initialized.
pub unsafe trait MoveNew: Sized {
  /// Move-construct `src` into `this`, effectively re-pinning it at a new
  /// location.
  ///
  /// # Safety
  ///
  /// The same safety requirements of [`New::new()`] apply, but, in addition,
  /// `*src` must not be used after this function is called, because it has
  /// effectively been destroyed.
  unsafe fn move_new(
    src: Pin<MoveRef<Self>>,
    this: Pin<&mut MaybeUninit<Self>>,
  );
}

/// Returns a [`New`] that forwards to [`MoveNew`].
///
/// ```
/// # use moveit::{MoveRef, moveit, new};
/// let foo = Box::new(42);
/// moveit! {
///   let bar = &move foo;
///   let baz = new::mov(bar);
/// }
/// ```
#[inline]
pub fn mov<'a, T, MS>(ptr: MS) -> impl New<Output = T>
where
  MS: MoveSource<'a, T>,
  T: MoveNew,
  MS::Storage: 'a
{
  unsafe {
    new::by_raw(move |this| {
      MoveNew::move_new(MS::get_move_source(ptr, slot!(#[dropping])), this);
    })
  }
}

/// Does movey stuff.
pub trait MoveSource<'frame, T> {
  /// Underlying storage for the movey thing.
  type Storage;
  /// Actually does movey stuff.
  fn get_move_source(
    self,
    storage: DroppingSlot<'frame, Self::Storage>,
  ) -> Pin<MoveRef<T>>;
}

impl<'frame, T, P> MoveSource<'frame, T> for Pin<P>
where
  P: Deref<Target = T> + DerefMove + 'frame,
{
  type Storage = P::Storage;
  fn get_move_source(
    self,
    storage: DroppingSlot<'frame, P::Storage>,
  ) -> Pin<MoveRef<T>> {
    Pin::as_move(self, storage)
  }
}
