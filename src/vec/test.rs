// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance new the License.
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

use std::mem;
use std::vec::Vec as StdVec;

use crate::new;
use crate::test_util::LeakCheck;
use crate::test_util::Tracked;
use crate::vec::Vec;
use crate::moveit;

#[test]
fn new() {
  let v = Vec::<i32>::new();
  assert_eq!(v.len(), 0);
  assert_eq!(v.capacity(), 0);
  assert_eq!(v, [0i32; 0]);
}

#[test]
fn new_zst() {
  let v = Vec::<()>::new();
  assert_eq!(v.len(), 0);
  assert_eq!(v.capacity(), usize::MAX);
  assert_eq!(v, [(); 0]);
  assert_ne!(v, [()]);
}

#[test]
fn with_capacity() {
  let v = Vec::<i32>::with_capacity(32);
  assert_eq!(v.len(), 0);
  assert_eq!(v.capacity(), 32);
  assert_eq!(v, [0i32; 0]);
}

#[test]
#[should_panic]
#[cfg_attr(miri, ignore)]
fn with_capacity_too_big() {
  let _ = Vec::<i32>::with_capacity(isize::MAX as usize / 4 + 1);
}

#[test]
fn with_capacity_zst() {
  let v = Vec::<()>::with_capacity(32);
  assert_eq!(v.len(), 0);
  assert_eq!(v.capacity(), usize::MAX);
  assert_eq!(v, [(); 0]);
  assert_ne!(v, [()]);
}

#[test]
fn from_raw_parts() {
  let mut v = Vec::from([1, 2, 3, 4, 5]);
  v.push(new::of(6));

  assert_eq!(v, [1, 2, 3, 4, 5, 6]);
  assert_eq!(v.len(), 6);
  assert_eq!(v.capacity(), Vec::<i32>::MIN_CAPACITY);

  let ptr = v.as_mut_ptr();
  let len = v.len();
  let cap = v.capacity();
  mem::forget(v);

  let v = unsafe { Vec::from_raw_parts(ptr, len, cap) };
  assert_eq!(v, [1, 2, 3, 4, 5, 6]);
  assert_eq!(v.len(), 6);
  assert_eq!(v.capacity(), Vec::<i32>::MIN_CAPACITY);
}

#[test]
fn of() {
  let _lc = LeakCheck::start();

  let v = Vec::of((0..32).map(|i| Tracked::new(i)));
  let ints = v.iter().map(|x| x.get()).collect::<StdVec<_>>();
  assert_eq!(ints, (0..32).collect::<StdVec<_>>());
}

#[test]
fn of_zst() {
  let v = Vec::of((0..32).map(|_| new::of(())));
  let ints = v.iter().map(|&x| x).collect::<StdVec<_>>();
  assert_eq!(ints, (0..32).map(|_| ()).collect::<StdVec<_>>());
}

#[test]
fn into_unpin() {
  let v = Vec::from([1, 2, 3, 4, 5]);
  let v2 = StdVec::from([1, 2, 3, 4, 5]);
  assert_eq!(v, v2);

  let v = v.into_unpin();
  assert_eq!(v, v2);
}

#[test]
fn reserve() {
  let mut x = Vec::from([1, 2, 3, 4, 5]);
  x.reserve(100);
  assert!(x.capacity() >= 105);

  x.reserve(10000);
  assert!(x.capacity() >= 10105);
}

#[test]
#[should_panic]
fn reserve_too_big() {
  let mut x = Vec::from([1, 2, 3, 4, 5]);
  x.reserve(isize::MAX as usize / 4);
}

// fn shrink_to_fit();

#[test]
fn push() {
  let _lc = LeakCheck::start();

  // Use a shorter length for miri to finish in a reasonable timeframe.
  let len = if cfg!(miri) {
    64
  } else {
    1024
  };

  let mut v = Vec::new();
  for i in 0..len {
    v.push(Tracked::new(i));
  }
}

#[test]
fn truncate() {
  let _lc = LeakCheck::start();

  let mut v = Vec::new();
  for i in 0..32 {
    v.push(Tracked::new(i));
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
  let _lc = LeakCheck::start();

  let mut v = Vec::new();
  for i in 0..32 {
    v.push(Tracked::new(i));
  }
  v.clear();
  assert!(v.is_empty());
}

#[test]
fn insert_middle() {
  let _lc = LeakCheck::start();

  let mut v = Vec::of((0..29).map(|i| Tracked::new(i)));
  v.insert(17, Tracked::new(5));
  assert_eq!(v[17].get(), 5);
  assert_eq!(v.len(), 30);
}

#[test]
fn insert_middle_power_of_two() {
  let _lc = LeakCheck::start();

  let mut v = Vec::of((0..32).map(|i| Tracked::new(i)));
  v.insert(17, Tracked::new(5));
  assert_eq!(v[17].get(), 5);
  assert_eq!(v.len(), 33);
}

#[test]
fn remove_middle() {
  let _lc = LeakCheck::start();

  let mut v = Vec::of((0..29).map(|i| Tracked::new(i)));
  moveit!(let x = v.remove(17));
  assert_eq!(x.get(), 17);
  assert_eq!(v[17].get(), 18);
  assert_eq!(v.len(), 28);
}

#[test]
fn remove_end() {
  let _lc = LeakCheck::start();

  let mut v = Vec::of((0..29).map(|i| Tracked::new(i)));
  moveit!(let x = v.remove(28));
  assert_eq!(x.get(), 28);
  assert_eq!(v[27].get(), 27);
  assert_eq!(v.len(), 28);
}

#[test]
fn remove_swap_middle() {
  let _lc = LeakCheck::start();

  let mut v = Vec::of((0..29).map(|i| Tracked::new(i)));
  moveit!(let x = v.swap_remove(17));
  assert_eq!(x.get(), 17);
  assert_eq!(v[17].get(), 28);
  assert_eq!(v.len(), 28);
}

#[test]
fn remove_swap_end() {
  let _lc = LeakCheck::start();

  let mut v = Vec::of((0..29).map(|i| Tracked::new(i)));
  moveit!(let x = v.swap_remove(28));
  assert_eq!(x.get(), 28);
  assert_eq!(v[27].get(), 27);
  assert_eq!(v.len(), 28);
}

#[test]
fn pop() {
  let _lc = LeakCheck::start();

  let mut z = 28;
  let mut v = Vec::of((0..29).map(|i| Tracked::new(i)));
  while let Some(x) = v.pop() {
    moveit!(let x = x);
    assert_eq!(x.get(), z);
    z -= 1;
  }
  assert!(v.is_empty());
}

#[test]
fn append() {
  let _lc = LeakCheck::start();

  let mut v = Vec::of((0..29).map(|i| Tracked::new(i)));
  let mut w = Vec::of((0..13).map(|i| Tracked::new(i)));
  v.append(&mut w);

  assert_eq!(v.len(), 29 + 13);
  assert!(w.is_empty());
  assert_eq!(&v[..29], (0..29).collect::<StdVec<_>>().as_slice());
  assert_eq!(&v[29..], (0..13).collect::<StdVec<_>>().as_slice());
}

#[test]
fn append_empty() {
  let _lc = LeakCheck::start();

  let mut v = Vec::of((0..29).map(|i| Tracked::new(i)));
  let v_old = v.clone();
  let mut w = Vec::new();
  v.append(&mut w);

  assert_eq!(v, v_old);
}

#[test]
fn drain_nothing() {
  let _lc = LeakCheck::start();

  let mut v = Vec::of((0..29).map(|i| Tracked::new(i)));
  assert!(Vec::drain(moveit!(&move &mut v), ..0).next().is_none());
}