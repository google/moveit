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

//! Tests for `moveit::Vec`.

use core::cell::Cell;
use core::fmt;
use core::mem::MaybeUninit;
use core::pin::Pin;

use std::vec::Vec as StdVec;

use crate::move_ref::MoveRef;
use crate::new;
use crate::new::CopyNew;
use crate::new::MoveNew;
use crate::new::New;
use crate::new::Swap;
use crate::vec::Vec;

/// Tracks that all values are correctly destroyed.
struct LeakCheck {
  count: Cell<usize>,
}

impl LeakCheck {
  pub fn inc(&self) {
    self.count.set(self.count.get() + 1)
  }

  pub fn dec(&self) {
    self.count.set(
      self
        .count
        .get()
        .checked_sub(1)
        .expect("leak detection count underflowed!"),
    )
  }

  pub fn check(&self) {
    assert!(
      self.count.get() == 0,
      "{} values were leaked",
      self.count.get()
    )
  }
}

impl Drop for LeakCheck {
  fn drop(&mut self) {
    self.check();
  }
}

thread_local! {
  static LEAK_CHECK: LeakCheck = LeakCheck { count: Cell::new(0) };
}

/// Tracks its moves; asserts on destruction if it was not moved around
/// correctly.
pub struct Tracked<T: fmt::Debug = ()> {
  inner: Option<T>,
  address: usize,
}

impl Tracked {
  pub fn new() -> impl New<Output = Self> {
    Self::with(())
  }
}

impl<T: fmt::Debug> Tracked<T> {
  pub fn with(val: T) -> impl New<Output = Self> {
    new::of(Self {
      inner: Some(val),
      address: 0,
    })
    .with(|this| unsafe {
      LEAK_CHECK.with(|c| c.inc());
      let this = Pin::into_inner_unchecked(this);
      this.address = this as *mut Self as usize;

      eprintln!("new: {:?}", this);
    })
  }
}

unsafe impl<T: fmt::Debug> MoveNew for Tracked<T> {
  unsafe fn move_new(
    src: Pin<MoveRef<Self>>,
    this: Pin<&mut MaybeUninit<Self>>,
  ) {
    let mut src = Pin::into_inner_unchecked(src);
    let this = Pin::into_inner_unchecked(this);

    LEAK_CHECK.with(|c| c.inc());
    let address = this as *mut _ as usize;
    this.write(Self {
      inner: Some(src.inner.take().expect("double-move!")),
      address,
    });

    eprintln!("move: {:?} -> {:?}", &*src, this.assume_init_mut());
  }
}

unsafe impl<T: fmt::Debug + Clone> CopyNew for Tracked<T> {
  unsafe fn copy_new(src: &Self, this: Pin<&mut MaybeUninit<Self>>) {
    let this = Pin::into_inner_unchecked(this);

    LEAK_CHECK.with(|c| c.inc());
    let address = this as *mut _ as usize;
    this.write(Self {
      inner: src.inner.clone(),
      address,
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
    eprintln!("delete: {:?}", self);
    let here = self as *mut _ as usize;
    assert!(
      here == self.address,
      "incorrectly destroyed {:?} at {:p}",
      self,
      self
    );
    LEAK_CHECK.with(|c| c.dec())
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

#[test]
fn push() {
  let mut v = Vec::new();
  for _ in 0..1024 {
    v.push(Tracked::new());
  }
}

#[test]
fn truncate() {
  let mut v = Vec::new();
  for _ in 0..32 {
    v.push(Tracked::new());
  }

  assert_eq!(v.len(), 32);
  v.truncate(18);
  assert_eq!(v.len(), 18);
  v.truncate(12);
  assert_eq!(v.len(), 12);
  v.truncate(5);
  assert_eq!(v.len(), 5);
}

#[test]
fn clear() {
  let mut v = Vec::new();
  for _ in 0..32 {
    v.push(Tracked::new());
  }
  v.clear();
  assert!(v.is_empty());
}

#[test]
fn from_constructors() {
  let v = Vec::of((0..32).map(|i| Tracked::with(i)));
  let ints = v.iter().map(|x| x.inner.unwrap()).collect::<StdVec<_>>();
  assert_eq!(ints, (0..32).collect::<StdVec<_>>());
}

#[test]
fn insert_middle() {
  let mut v = Vec::of((0..29).map(|i| Tracked::with(i)));
  v.insert(17, Tracked::with(5));
  assert_eq!(v[17].inner, Some(5));
  assert_eq!(v.len(), 30);
}

#[test]
fn insert_middle_power_of_two() {
  let mut v = Vec::of((0..32).map(|i| Tracked::with(i)));
  v.insert(17, Tracked::with(5));
  assert_eq!(v[17].inner, Some(5));
  assert_eq!(v.len(), 33);
}

#[test]
fn remove_middle() {
  let mut v = Vec::of((0..29).map(|i| Tracked::with(i)));
  v.remove(17);
  assert_eq!(v[17].inner, Some(18));
  assert_eq!(v.len(), 28);
}
