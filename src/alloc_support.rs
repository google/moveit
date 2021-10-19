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

use crate::new::Emplace;
use crate::new::TryNew;
use crate::move_ref::DerefMove;
use crate::move_ref::MoveRef;

unsafe impl<T> DerefMove for Box<T> {
  type Uninit = Box<MaybeUninit<T>>;

  #[inline]
  fn deinit(self) -> Self::Uninit {
    unsafe { Box::from_raw(Box::into_raw(self).cast::<MaybeUninit<T>>()) }
  }

  #[inline]
  unsafe fn deref_move(this: &mut Self::Uninit) -> MoveRef<Self::Target> {
    MoveRef::new_unchecked(&mut *(&mut **this as *mut MaybeUninit<T> as *mut T))
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
