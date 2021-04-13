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

use core::mem;
use core::mem::MaybeUninit;
use core::pin::Pin;

use alloc::alloc::Layout;
use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::sync::Arc;

use crate::ctor::Emplace;
use crate::ctor::TryCtor;
use crate::unique::DerefMove;
use crate::unique::MaybeUnique;
use crate::unique::OuterDrop;

unsafe impl<T> OuterDrop for Box<T> {
  unsafe fn outer_drop(this: *mut Self) {
    if mem::size_of::<T>() == 0 {
      return;
    }

    // SAFETY: `Box<T>` and `*mut T` are guaranteed to be interconvertible.
    let ptr = this.cast::<*mut T>().read();
    alloc::alloc::dealloc(ptr.cast::<u8>(), Layout::new::<T>());
  }
}

unsafe impl<T> OuterDrop for Rc<T> {
  unsafe fn outer_drop(this: *mut Self) {
    // Unfortunately, we need to actually materialize the `Rc` to get the inner
    // pointer out.
    let ptr = Rc::as_ptr(&*this);
    let _ = Rc::from_raw(ptr.cast::<MaybeUninit<T>>());
  }
}

unsafe impl<T> OuterDrop for Arc<T> {
  unsafe fn outer_drop(this: *mut Self) {
    // Unfortunately, we need to actually materialize the `Arc` to get the inner
    // pointer out.
    let ptr = Arc::as_ptr(&*this);
    let _ = Arc::from_raw(ptr.cast::<MaybeUninit<T>>());
  }
}

unsafe impl<T> DerefMove for Box<T> {}

unsafe impl<T> MaybeUnique for Rc<T> {
  fn is_unique(&self) -> bool {
    Rc::strong_count(self) == 1 && Rc::weak_count(self) == 1
  }
}

unsafe impl<T> MaybeUnique for Arc<T> {
  fn is_unique(&self) -> bool {
    // SAFETY: There are no atomic subtleties here: if we observe
    // this particular refcount, it is impossible for more weak pointers to
    // materialize from the aether. The *_count() methods are SeqCst.
    Arc::strong_count(self) == 1 && Arc::weak_count(self) == 1
  }
}

impl<T> Emplace<T> for Box<T> {
  fn try_emplace<C: TryCtor<Output = T>>(c: C) -> Result<Pin<Self>, C::Error> {
    let mut uninit = Box::new(MaybeUninit::<T>::uninit());
    unsafe {
      let pinned = Pin::new_unchecked(&mut *uninit);
      c.try_ctor(pinned)?;
      Ok(Pin::new_unchecked(Box::from_raw(
        Box::into_raw(uninit).cast::<T>(),
      )))
    }
  }
}

impl<T> Emplace<T> for Rc<T> {
  fn try_emplace<C: TryCtor<Output = T>>(c: C) -> Result<Pin<Self>, C::Error> {
    let uninit = Rc::new(MaybeUninit::<T>::uninit());
    unsafe {
      let pinned = Pin::new_unchecked(&mut *(Rc::as_ptr(&uninit) as *mut _));
      c.try_ctor(pinned)?;
      Ok(Pin::new_unchecked(Rc::from_raw(
        Rc::into_raw(uninit).cast::<T>(),
      )))
    }
  }
}

impl<T> Emplace<T> for Arc<T> {
  fn try_emplace<C: TryCtor<Output = T>>(c: C) -> Result<Pin<Self>, C::Error> {
    let uninit = Arc::new(MaybeUninit::<T>::uninit());
    unsafe {
      let pinned = Pin::new_unchecked(&mut *(Arc::as_ptr(&uninit) as *mut _));
      c.try_ctor(pinned)?;
      Ok(Pin::new_unchecked(Arc::from_raw(
        Arc::into_raw(uninit).cast::<T>(),
      )))
    }
  }
}
