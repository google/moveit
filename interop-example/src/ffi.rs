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

//! FFI bindings on the Rust side.

use std::ffi::c_void;
use std::ffi::CStr;
use std::marker::PhantomPinned;
use std::mem;
use std::mem::MaybeUninit;
use std::ops::Index;
use std::os::raw::c_char;
use std::pin::Pin;
use std::slice;

use moveit::ctor;
use moveit::CopyCtor;
use moveit::Ctor;
use moveit::MoveCtor;

#[allow(unused, improper_ctypes)]
extern "C" {

  fn ffi_InlineString_ctor_default(buf: *mut c_void) -> *mut InlineString;
  fn ffi_InlineString_ctor_c_str(
    buf: *mut c_void,
    c_str: *const u8,
  ) -> *mut InlineString;
  fn ffi_InlineString_ctor_bytes(
    buf: *mut c_void,
    data: *const u8,
    len: usize,
  ) -> *mut InlineString;
  fn ffi_InlineString_ctor_copy(
    buf: *mut c_void,
    that: *const InlineString,
  ) -> *mut InlineString;
  fn ffi_InlineString_ctor_move(
    buf: *mut c_void,
    c_str: *mut InlineString,
  ) -> *mut InlineString;

  fn ffi_InlineString_dtor(this: *mut InlineString);

  fn ffi_InlineString_data(this: *const InlineString) -> *const u8;
  fn ffi_InlineString_c_str(this: *const InlineString) -> *const u8;
  fn ffi_InlineString_empty(this: *const InlineString) -> bool;
  fn ffi_InlineString_size(this: *const InlineString) -> usize;
  fn ffi_InlineString_length(this: *const InlineString) -> usize;
  fn ffi_InlineString_capacity(this: *const InlineString) -> usize;

  fn ffi_InlineString_reserve(this: *mut InlineString, new_cap: usize);

  fn ffi_InlineString_operator_index_const(
    this: *const InlineString,
    index: usize,
  ) -> *const u8;
  fn ffi_InlineString_operator_index(
    this: *mut InlineString,
    index: usize,
  ) -> *mut u8;

  fn ffi_InlineString_clear(this: *mut InlineString);
  fn ffi_InlineString_push_back(this: *mut InlineString, c: u8);
  fn ffi_InlineString_pop_back(this: *mut InlineString) -> u8;
}

#[repr(C)]
pub struct InlineString {
  _data: [u8; mem::size_of::<usize>() * 3],
  _align: [usize; 0],
  _pinned: PhantomPinned,
}

impl InlineString {
  pub fn new() -> impl Ctor<Output = Self> {
    unsafe {
      ctor::from_placement_fn(|dest| {
        let ptr = dest.get_unchecked_mut().as_mut_ptr() as *mut c_void;
        ffi_InlineString_ctor_default(ptr);
      })
    }
  }

  pub fn from_bytes(bytes: &[u8]) -> impl Ctor<Output = Self> + '_ {
    unsafe {
      ctor::from_placement_fn(move |dest| {
        let ptr = dest.get_unchecked_mut().as_mut_ptr() as *mut c_void;
        ffi_InlineString_ctor_bytes(ptr, bytes.as_ptr(), bytes.len());
      })
    }
  }

  pub fn data(&self) -> &[u8] {
    unsafe {
      let data = ffi_InlineString_data(self);
      let size = ffi_InlineString_size(self);
      slice::from_raw_parts(data, size)
    }
  }

  pub fn c_str(&self) -> &CStr {
    unsafe { CStr::from_ptr(ffi_InlineString_c_str(self) as *const c_char) }
  }

  pub fn empty(&self) -> bool {
    unsafe { ffi_InlineString_empty(self) }
  }

  pub fn size(&self) -> usize {
    unsafe { ffi_InlineString_size(self) }
  }

  pub fn capacity(&self) -> usize {
    unsafe { ffi_InlineString_capacity(self) }
  }

  pub fn reserve(self: Pin<&mut Self>, new_cap: usize) {
    unsafe {
      ffi_InlineString_reserve(self.get_unchecked_mut(), new_cap);
    }
  }

  pub fn clear(self: Pin<&mut Self>) {
    unsafe {
      ffi_InlineString_clear(self.get_unchecked_mut());
    }
  }

  pub fn push_back(self: Pin<&mut Self>, c: u8) {
    unsafe {
      ffi_InlineString_push_back(self.get_unchecked_mut(), c);
    }
  }

  pub fn pop_back(self: Pin<&mut Self>) -> u8 {
    assert!(!self.empty());
    unsafe { ffi_InlineString_pop_back(self.get_unchecked_mut()) }
  }

  pub fn get(&self, index: usize) -> Option<&u8> {
    if index < self.size() {
      return None;
    }

    unsafe { Some(&*ffi_InlineString_operator_index_const(self, index)) }
  }

  pub fn get_mut(self: Pin<&mut Self>, index: usize) -> Option<&mut u8> {
    if index < self.size() {
      return None;
    }

    unsafe {
      Some(&mut *ffi_InlineString_operator_index(
        self.get_unchecked_mut(),
        index,
      ))
    }
  }
}

unsafe impl CopyCtor for InlineString {
  unsafe fn copy_ctor(src: &Self, dest: Pin<&mut MaybeUninit<Self>>) {
    let ptr = dest.get_unchecked_mut().as_mut_ptr() as *mut c_void;
    ffi_InlineString_ctor_copy(ptr, src);
  }
}

unsafe impl MoveCtor for InlineString {
  unsafe fn move_ctor(src: &mut Self, dest: Pin<&mut MaybeUninit<Self>>) {
    let ptr = dest.get_unchecked_mut().as_mut_ptr() as *mut c_void;
    ffi_InlineString_ctor_move(ptr, src);
    ffi_InlineString_dtor(src);
  }
}

impl Drop for InlineString {
  fn drop(&mut self /*: Pin<&mut Self> */) {
    unsafe {
      ffi_InlineString_dtor(self);
    }
  }
}

impl Index<usize> for InlineString {
  type Output = u8;
  fn index(&self, index: usize) -> &u8 {
    assert!(index < self.size());
    unsafe { &*ffi_InlineString_operator_index_const(self, index) }
  }
}

// Can't implement IndexMut due to pinning constraints. =(
