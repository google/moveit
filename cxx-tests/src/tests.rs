// Copyright 2022 Google LLC
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

use cxx::UniquePtr;
use moveit::moveit;
use moveit::Emplace;
use moveit::EmplaceUnpinned;

// Shared with C++
const UNINITIALIZED: u8 = 0;
const INITIALIZED: u8 = 1;
const METHOD_CALLED: u8 = 2;

#[cxx::bridge]
mod ffi {
  unsafe extern "C++" {
    include!("cxx_support_test_cpp.h");
    type Foo = super::bindgenish::Foo;
    fn CreateUninitializedFoo() -> *mut Foo;
    unsafe fn FreeUninitializedFoo(ptr: *mut Foo);

    fn foo_constructor(_this: Pin<&mut Foo>);
    unsafe fn foo_destructor(_this: *mut Foo);
    unsafe fn foo_move(_this: *mut Foo, src: *mut Foo);

    fn get_status(self: &Foo) -> u8;
    fn modify(self: Pin<&mut Foo>);
  }
  // Ensures that cxx creates bindings for UniquePtr<Foo>
  // even though that isn't used in any of the above APIs.
  impl UniquePtr<Foo> {}
}

mod bindgenish {
  use std::marker::PhantomData;
  use std::marker::PhantomPinned;
  use std::mem::MaybeUninit;
  use std::pin::Pin;

  use cxx::kind::Opaque;
  use cxx::type_id;
  use cxx::ExternType;

  use moveit::MakeCppStorage;
  use moveit::MoveNew;
  use moveit::New;

  #[repr(C)]
  pub struct Foo {
    // opaque
    _pin: PhantomData<PhantomPinned>,
    _data: [u32; 4],
  }

  unsafe impl ExternType for Foo {
    type Id = type_id!("Foo");
    type Kind = Opaque;
  }

  unsafe impl MakeCppStorage for Foo {
    unsafe fn allocate_uninitialized_cpp_storage() -> *mut Self {
      let foo = super::ffi::CreateUninitializedFoo();
      assert_eq!(foo.as_ref().unwrap().get_status(), super::UNINITIALIZED);
      foo
    }

    unsafe fn free_uninitialized_cpp_storage(ptr: *mut Self) {
      super::ffi::FreeUninitializedFoo(ptr);
    }
  }

  impl Foo {
    pub fn new() -> impl New<Output = Self> {
      unsafe {
        moveit::new::by_raw(|space| {
          // TODO can we get rid of the transmute?
          let space = std::mem::transmute(space);
          super::ffi::foo_constructor(space)
        })
      }
    }
  }

  unsafe impl MoveNew for Foo {
    unsafe fn move_new(
      mut src: Pin<moveit::MoveRef<Self>>,
      this: Pin<&mut MaybeUninit<Self>>,
    ) {
      let src: &mut _ = ::std::pin::Pin::into_inner_unchecked(src.as_mut());
      let this = std::mem::transmute(this);
      super::ffi::foo_move(this, src);
      super::ffi::foo_destructor(src);
    }
  }
}

#[test]
fn test_stack_emplacement() {
  moveit! {
    let mut foo = bindgenish::Foo::new();
  }
  assert_eq!(foo.get_status(), INITIALIZED);
  foo.as_mut().modify();
  assert_eq!(foo.get_status(), METHOD_CALLED);
}

#[test]
fn test_box_emplacement() {
  let mut foo = Box::emplace(bindgenish::Foo::new());
  assert_eq!(foo.get_status(), INITIALIZED);
  foo.as_mut().modify();
  assert_eq!(foo.get_status(), METHOD_CALLED);
}

#[test]
fn test_unique_ptr_emplacement() {
  let mut foo = UniquePtr::emplace(bindgenish::Foo::new());
  assert_eq!(foo.get_status(), INITIALIZED);
  foo.pin_mut().modify();
  assert_eq!(foo.get_status(), METHOD_CALLED);
}

#[test]
fn test_move_from_up() {
  let mut foo = UniquePtr::emplace(bindgenish::Foo::new());
  assert_eq!(foo.get_status(), INITIALIZED);
  foo.pin_mut().modify();
  assert_eq!(foo.get_status(), METHOD_CALLED);
  moveit! {
    let mut foo2 = moveit::mov_up(foo);
  }
  assert_eq!(foo2.get_status(), METHOD_CALLED);
}
