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
use core::pin::Pin;

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::sync::Arc;

use crate::move_ref::DerefMove;
use crate::move_ref::MoveRef;
use crate::new::Emplace;
use crate::new::TryNew;
use crate::slot::DroppingSlot;

unsafe impl<T> DerefMove for Box<T> {
  type Storage = Box<MaybeUninit<T>>;

  #[inline]
  fn deref_move<'frame>(
    this: MoveRef<'frame, Self>,
    storage: &'frame mut DroppingSlot<Self::Storage>,
  ) -> MoveRef<'frame, Self::Target> {
    let this = MoveRef::into_inner(this);
    let cast =
      unsafe { Box::from_raw(Box::into_raw(this).cast::<MaybeUninit<T>>()) };
    let storage = storage.put(cast);

    unsafe { MoveRef::new_unchecked(storage.assume_init_mut()) }
  }
}

impl<T> Emplace<T> for Box<T> {
  fn try_emplace<N: TryNew<Output = T>>(n: N) -> Result<Pin<Self>, N::Error> {
    let mut uninit = Box::new(MaybeUninit::<T>::uninit());
    unsafe {
      let pinned = Pin::new_unchecked(&mut *uninit);
      n.try_new(pinned)?;
      Ok(Pin::new_unchecked(Box::from_raw(
        Box::into_raw(uninit).cast::<T>(),
      )))
    }
  }
}

impl<T> Emplace<T> for Rc<T> {
  fn try_emplace<N: TryNew<Output = T>>(n: N) -> Result<Pin<Self>, N::Error> {
    let uninit = Rc::new(MaybeUninit::<T>::uninit());
    unsafe {
      let pinned = Pin::new_unchecked(&mut *(Rc::as_ptr(&uninit) as *mut _));
      n.try_new(pinned)?;
      Ok(Pin::new_unchecked(Rc::from_raw(
        Rc::into_raw(uninit).cast::<T>(),
      )))
    }
  }
}

impl<T> Emplace<T> for Arc<T> {
  fn try_emplace<N: TryNew<Output = T>>(n: N) -> Result<Pin<Self>, N::Error> {
    let uninit = Arc::new(MaybeUninit::<T>::uninit());
    unsafe {
      let pinned = Pin::new_unchecked(&mut *(Arc::as_ptr(&uninit) as *mut _));
      n.try_new(pinned)?;
      Ok(Pin::new_unchecked(Arc::from_raw(
        Arc::into_raw(uninit).cast::<T>(),
      )))
    }
  }
}
