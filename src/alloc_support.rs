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

//! Support for the `alloc` crate, when available.

use core::mem::MaybeUninit;
use core::ops::Deref;
use core::pin::Pin;

use alloc::boxed::Box;

use crate::move_ref::MoveRef;
use crate::move_ref::{AsMove, DerefMove};
use crate::slot::DroppingSlot;

impl<T> AsMove<Self> for Box<T> {
  type Storage = <Self as DerefMove>::Storage;

  fn as_move<'frame>(
    self,
    storage: DroppingSlot<'frame, Self::Storage>,
  ) -> Pin<MoveRef<'frame, <Self as Deref>::Target>>
  where
    Self: 'frame,
  {
    MoveRef::into_pin(self.deref_move(storage))
  }
}

unsafe impl<T> DerefMove for Box<T> {
  type Storage = Box<MaybeUninit<T>>;

  #[inline]
  fn deref_move<'frame>(
    self,
    storage: DroppingSlot<'frame, Self::Storage>,
  ) -> MoveRef<'frame, Self::Target>
  where
    Self: 'frame,
  {
    let cast =
      unsafe { Box::from_raw(Box::into_raw(self).cast::<MaybeUninit<T>>()) };

    let (storage, drop_flag) = storage.put(cast);
    unsafe { MoveRef::new_unchecked(storage.assume_init_mut(), drop_flag) }
  }
}

#[cfg(test)]
mod tests {
  use crate::move_ref::test::Immovable;
  use crate::moveit;
  use crate::new::mov;
  use crate::Emplace;

  #[test]
  fn test_mov_box() {
    let foo = Box::emplace(Immovable::new());
    moveit!(let _foo = mov(foo));
  }
}
