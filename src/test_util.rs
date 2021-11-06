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

//! Test utilities for `Vec`, which allow for ensuring that values are moved
//! and destroyed correctly.

use core::cell::Cell;
use core::fmt;
use core::marker::PhantomData;
use core::marker::PhantomPinned;
use core::mem::MaybeUninit;
use core::pin::Pin;

use crate::move_ref::MoveRef;
use crate::new;
use crate::new::CopyNew;
use crate::new::MoveNew;
use crate::new::New;
use crate::new::Swap;

/// A leak detector for values created in the current thread.
///
/// All this does is make sure that the number of `on_ctor()` and `on_dtor()`
/// calls is equal when this guard is destroyed.
///
/// Only one `LeakCheck` may exist per thread at a time.
pub struct LeakCheck(PhantomData<*mut u8>);

thread_local! {
  static LEAK_COUNTER: Cell<Option<usize>> = Cell::new(None);
}

impl LeakCheck {
  /// Starts leak tracking for this thread, which ends when this value is
  /// dropped.
  pub fn start() -> Self {
    LEAK_COUNTER.with(|c| match c.get() {
      Some(_) => panic!("leak counter initialized twice"),
      None => c.set(Some(0)),
    });
    Self(PhantomData)
  }

  /// Registers that a value was created.
  pub fn on_ctor() {
    LEAK_COUNTER.with(|c| {
      let val = c.get().expect("leak counter not initialized");
      let inc = val + 1;
      eprintln!("ctor: {} -> {}", val, inc);
      c.set(Some(inc));
    })
  }

  /// Registers that a value was destroyed.
  pub fn on_dtor() {
    LEAK_COUNTER.with(|c| {
      let val = c.get().expect("leak counter not initialized");
      let dec = val.checked_sub(1).expect("leak counter underflow");
      eprintln!("dtor: {} -> {}", val, dec);
      c.set(Some(dec));
    })
  }

  /// Checks that all objects tracked by leak-checking have been destroyed.
  pub fn check() {
    let count = LEAK_COUNTER
      .with(|c| c.get())
      .expect("leak counter not initialized");
    assert!(count == 0, "{} values were leaked", count)
  }
}

impl Drop for LeakCheck {
  fn drop(&mut self) {
    Self::check();
    LEAK_COUNTER.with(|c| c.set(None));
  }
}

/// Tracks the movements of a value `T`.
///
/// This pinned type ensures that:
/// - Its address on destruction is the address it was constructed at.
/// - Uses [`LeakCheck`] to ensure it is correctly destroyed on scope exit.
///
/// This type is `MoveCtor`, `CopyCtor`, and `Swap`.
pub struct Tracked<T: fmt::Debug> {
  inner: Option<T>,
  address: usize,
  _pinned: PhantomPinned,
}

impl<T: fmt::Debug> Tracked<T> {
  /// Creates a new `Tracked` wrapping `val`.
  pub fn new(val: T) -> impl New<Output = Self> {
    new::of(Self {
      inner: Some(val),
      address: 0,
      _pinned: PhantomPinned,
    })
    .with(|this| unsafe {
      LeakCheck::on_ctor();

      let this = Pin::into_inner_unchecked(this);
      this.address = this as *mut Self as usize;

      eprintln!("new: {:?}", this);
    })
  }

  pub fn get(&self) -> T
  where
    T: Clone,
  {
    self.inner.clone().expect("use-after-free")
  }
}

unsafe impl<T: fmt::Debug> MoveNew for Tracked<T> {
  unsafe fn move_new(
    src: Pin<MoveRef<Self>>,
    this: Pin<&mut MaybeUninit<Self>>,
  ) {
    LeakCheck::on_ctor();

    let mut src = Pin::into_inner_unchecked(src);
    let this = Pin::into_inner_unchecked(this);

    let address = this as *mut _ as usize;
    this.write(Self {
      inner: Some(src.inner.take().expect("double-move")),
      address,
      _pinned: PhantomPinned,
    });

    eprintln!("move: {:?} -> {:?}", &*src, this.assume_init_mut());
  }
}

unsafe impl<T: fmt::Debug + Clone> CopyNew for Tracked<T> {
  unsafe fn copy_new(src: &Self, this: Pin<&mut MaybeUninit<Self>>) {
    LeakCheck::on_ctor();

    let this = Pin::into_inner_unchecked(this);
    let address = this as *mut _ as usize;
    this.write(Self {
      inner: src.inner.clone(),
      address,
      _pinned: PhantomPinned,
    });

    eprintln!("copy: {:?} -> {:?}", src, this.assume_init_mut());
  }
}

impl<T: fmt::Debug> Swap for Tracked<T> {
  fn swap_with(self: Pin<&mut Self>, that: Pin<&mut Self>) {
    unsafe {
      let zelf = Pin::into_inner_unchecked(self);
      let that = Pin::into_inner_unchecked(that);

      core::mem::swap(&mut zelf.inner, &mut that.inner);

      eprintln!("swap: {:?} -> {:?}", zelf, that);
    }
  }
}

impl<T: fmt::Debug> Drop for Tracked<T> {
  fn drop(&mut self) {
    LeakCheck::on_dtor();

    eprintln!("delete: {:?}", self);
    let here = self as *mut _ as usize;
    assert!(
      here == self.address,
      "incorrectly destroyed {:?} at {:p}",
      self,
      self
    );
  }
}

impl<T: fmt::Debug> fmt::Debug for Tracked<T> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(
      f,
      "Tracked({:?} @ {:p})",
      self.inner, self.address as *mut u8
    )
  }
}

impl<T: PartialEq + fmt::Debug> PartialEq<T> for Tracked<T> {
  fn eq(&self, that: &T) -> bool {
    self.inner.as_ref() == Some(that)
  }
}

impl<T: PartialEq + fmt::Debug> PartialEq for Tracked<T> {
  fn eq(&self, that: &Self) -> bool {
    self.inner == that.inner
  }
}