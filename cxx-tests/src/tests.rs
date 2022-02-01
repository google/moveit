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

use once_cell::sync::OnceCell;
use std::sync::Mutex;
use std::sync::MutexGuard;

use cxx::UniquePtr;
use moveit::moveit;
use moveit::Emplace;
use moveit::EmplaceUnpinned;

#[cxx::bridge]
mod ffi {
  #[derive(Debug)]
  enum Status {
    Unallocated,
    Allocated,
    Initialized,
    Destructed,
    Deallocated,
    DeallocatedUninitialized,
  }

  unsafe extern "C++" {
    include!("cxx_support_test_cpp.h");
    type Foo = super::bindgenish::Foo;
    fn foo_create_uninitialized() -> *mut Foo;
    unsafe fn foo_free_uninitialized(ptr: *mut Foo);
    fn foo_constructor(_this: Pin<&mut Foo>);
    unsafe fn foo_destructor(_this: *mut Foo);
    unsafe fn foo_move(_this: *mut Foo, src: *mut Foo);

    type Bar = super::bindgenish::Bar;
    fn bar_create_uninitialized() -> *mut Bar;
    unsafe fn bar_free_uninitialized(ptr: *mut Bar);
    fn bar_constructor(_this: Pin<&mut Bar>);
    unsafe fn bar_destructor(_this: *mut Bar);
    unsafe fn bar_move(_this: *mut Bar, src: *mut Bar);

    fn get_a(self: &Foo) -> bool;
    fn modify(self: Pin<&mut Foo>);
    fn do_nothing(self: &Bar);

    fn reset_status();
    fn get_status() -> Status;
  }
  // Ensures that cxx creates bindings for UniquePtr<Foo>
  // even though that isn't used in any of the above APIs.
  impl UniquePtr<Foo> {}
  impl UniquePtr<Bar> {}
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
      super::ffi::foo_create_uninitialized()
    }

    unsafe fn free_uninitialized_cpp_storage(ptr: *mut Self) {
      super::ffi::foo_free_uninitialized(ptr);
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

  impl Drop for Foo {
    fn drop(&mut self) {
      unsafe { super::ffi::foo_destructor(self) };
    }
  }

  #[repr(C)]
  pub struct Bar {
    // opaque
    _pin: PhantomData<PhantomPinned>,
    _data: [u32; 4],
  }

  unsafe impl ExternType for Bar {
    type Id = type_id!("Bar");
    type Kind = Opaque;
  }

  unsafe impl MakeCppStorage for Bar {
    unsafe fn allocate_uninitialized_cpp_storage() -> *mut Self {
      let bar = super::ffi::bar_create_uninitialized();
      bar
    }

    unsafe fn free_uninitialized_cpp_storage(ptr: *mut Self) {
      super::ffi::bar_free_uninitialized(ptr);
    }
  }

  impl Bar {
    pub fn new() -> impl New<Output = Self> {
      unsafe {
        moveit::new::by_raw(|space| {
          // TODO can we get rid of the transmute?
          let space = std::mem::transmute(space);
          super::ffi::bar_constructor(space)
        })
      }
    }
  }

  unsafe impl MoveNew for Bar {
    unsafe fn move_new(
      mut src: Pin<moveit::MoveRef<Self>>,
      this: Pin<&mut MaybeUninit<Self>>,
    ) {
      let src: &mut _ = ::std::pin::Pin::into_inner_unchecked(src.as_mut());
      let this = std::mem::transmute(this);
      super::ffi::bar_move(this, src);
      super::ffi::bar_destructor(src);
    }
  }

  impl Drop for Bar {
    fn drop(&mut self) {
      unsafe { super::ffi::bar_destructor(self) };
    }
  }
}

/// Queries C++ to find the current state of object lifetimes.
/// Its main purpose is actually to sneakily enforce a mutex such that
/// tests do not run in parallel and corrupt that state.
struct StatusChecker<'a>(MutexGuard<'a, ()>);

impl<'a> StatusChecker<'a> {
  fn new() -> Self {
    static MUTEX: OnceCell<Mutex<()>> = OnceCell::new();
    let guard = MUTEX.get_or_init(|| Mutex::new(())).lock().unwrap();
    ffi::reset_status();
    Self(guard)
  }

  fn assert_status(&self, expected: ffi::Status) {
    assert_eq!(ffi::get_status(), expected);
  }
}

#[test]
fn test_stack_emplacement() {
  let status_checker = StatusChecker::new();
  {
    status_checker.assert_status(ffi::Status::Unallocated);
    moveit! {
      let mut bar = bindgenish::Bar::new();
    }
    status_checker.assert_status(ffi::Status::Initialized);
    bar.do_nothing(); // so Rust prolongs lifetime of bar
  }
  status_checker.assert_status(ffi::Status::Destructed);
}

#[test]
fn test_stack_emplacement_complex() {
  let status_checker = StatusChecker::new();
  {
    status_checker.assert_status(ffi::Status::Unallocated);
    moveit! {
      let mut foo = bindgenish::Foo::new();
    }
    status_checker.assert_status(ffi::Status::Initialized);
    assert_eq!(foo.get_a(), false);
    foo.as_mut().modify();
    assert_eq!(foo.get_a(), true);
  }
  status_checker.assert_status(ffi::Status::Destructed);
}

#[test]
fn test_box_emplacement() {
  let status_checker = StatusChecker::new();
  status_checker.assert_status(ffi::Status::Unallocated);
  {
    let bar = Box::emplace(bindgenish::Bar::new());
    status_checker.assert_status(ffi::Status::Initialized);
    bar.do_nothing(); // so Rust prolongs lifetime of bar
  }
  status_checker.assert_status(ffi::Status::Destructed);
}

#[test]
fn test_box_emplacement_complex() {
  let status_checker = StatusChecker::new();
  status_checker.assert_status(ffi::Status::Unallocated);
  {
    let mut foo = Box::emplace(bindgenish::Foo::new());
    status_checker.assert_status(ffi::Status::Initialized);
    assert_eq!(foo.get_a(), false);
    foo.as_mut().modify();
    assert_eq!(foo.get_a(), true);
  }
  status_checker.assert_status(ffi::Status::Destructed);
}

#[test]
fn test_unique_ptr_emplacement() {
  let status_checker = StatusChecker::new();
  status_checker.assert_status(ffi::Status::Unallocated);
  {
    let bar = UniquePtr::emplace(bindgenish::Bar::new());
    status_checker.assert_status(ffi::Status::Initialized);
    bar.do_nothing(); // so Rust prolongs lifetime of bar
  }
  // We have no custom operator delete so the last status
  // we record is merely 'destructed'
  status_checker.assert_status(ffi::Status::Destructed);
}

#[test]
fn test_unique_ptr_emplacement_complex() {
  let status_checker = StatusChecker::new();
  status_checker.assert_status(ffi::Status::Unallocated);
  {
    let mut foo = UniquePtr::emplace(bindgenish::Foo::new());
    status_checker.assert_status(ffi::Status::Initialized);
    assert_eq!(foo.get_a(), false);
    foo.pin_mut().modify();
    assert_eq!(foo.get_a(), true);
  }
  status_checker.assert_status(ffi::Status::Deallocated);
}

#[test]
fn test_move_from_up() {
  let status_checker = StatusChecker::new();
  status_checker.assert_status(ffi::Status::Unallocated);
  let bar = UniquePtr::emplace(bindgenish::Bar::new());
  status_checker.assert_status(ffi::Status::Initialized);
  {
    moveit! {
      let _bar2 = moveit::new::mov(bar);
    }
    // No custom operator::delete for this type
    status_checker.assert_status(ffi::Status::DeallocatedUninitialized);
  }
  status_checker.assert_status(ffi::Status::Destructed);
}

#[test]
fn test_move_from_up_complex() {
  let status_checker = StatusChecker::new();
  status_checker.assert_status(ffi::Status::Unallocated);
  let mut foo = UniquePtr::emplace(bindgenish::Foo::new());
  status_checker.assert_status(ffi::Status::Initialized);
  assert_eq!(foo.get_a(), false);
  foo.pin_mut().modify();
  assert_eq!(foo.get_a(), true);
  {
    moveit! {
      let mut foo2 = moveit::new::mov(foo);
    }
    // If this line determines the status to be DeallocatedUninitialized,
    // we've failed to call the overridden operator delete
    status_checker.assert_status(ffi::Status::Deallocated);
    assert_eq!(foo2.get_a(), true);
  }
  status_checker.assert_status(ffi::Status::Destructed);
}
