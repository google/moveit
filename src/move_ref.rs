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

//! Move references, for emulating `&move`.

#![allow(missing_docs, unused)]

use core::mem::MaybeUninit;
use core::ops::Deref;
use core::ops::DerefMut;
use core::pin::Pin;
use core::ptr;
use core::marker::Unpin;

#[cfg(doc)]
use alloc::{
  boxed::Box,
  rc::Rc,
  sync::Arc,
};

/// A library emulation of the theoretical `&move T` type.
/// 
/// A `MoveRef<'a, T>` represents a unique reference to `T` for the lifetime
/// `'a`. Unlike an `&mut T`, though, a `MoveRef<T>` is the *longest-lived* such
/// reference, entitling it to run `T`'s destructor. In other words,
/// `MoveRef<T>` owns its referent, but not its referent's storage.
/// See the [module docs][`crate::move_ref`] for more information.
/// 
/// The main mechanism for obtaining `MoveRef`s is the [`move_ref!()`] macro,
/// which is analogous to a theoretical `&move expr` operator. This actuates
/// a [`DerefMove`] implementation.
pub struct MoveRef<'a, T: ?Sized> {
  ptr: &'a mut T,
}

impl<'a, T: ?Sized> MoveRef<'a, T> {
  /// Create a new `MoveRef<T>` out of a mutable reference.
  /// 
  /// # Safety
  /// 
  /// `ptr` must satisfy the *longest-lived* criterion: after the return value
  /// goes out of scope, `ptr` must also be out-of-scope. Calling this function
  /// correctly is non-trivial, and should be left to [`move_ref!()`] instead.
  /// 
  /// In particular, if `ptr` outlives the returned `MoveRef`, it will point
  /// to dropped memory, which is UB.
  #[inline]
  pub unsafe fn new_unchecked(ptr: &'a mut T) -> Self {
    Self { ptr }
  }

  /// Convert a `MoveRef<T>` into a `Pin<MoveRef<T>>`.
  /// 
  /// Because we own the referent, we are entitled to pin it permanently. See
  /// [`Box::into_pin()`] for a standard-library equivalent.
  #[inline]
  pub fn into_pin(this: Self) -> Pin<Self> {
    unsafe { Pin::new_unchecked(this) }
  }
}

impl<'a, T> MoveRef<'a, T> {
  /// Consume the `MoveRef<T>`, returning the wrapped value.
  #[inline]
  pub fn into_inner(this: Self) -> T {
    let val = unsafe { ptr::read(this.ptr) };
    core::mem::forget(this);
    val
  }
}

impl<T: ?Sized> Deref for MoveRef<'_, T> {
  type Target = T;

  #[inline]
  fn deref(&self) -> &Self::Target {
    self.ptr
  }
}

impl<T: ?Sized> DerefMut for MoveRef<'_, T> {
  #[inline]
  fn deref_mut(&mut self) -> &mut Self::Target {
    self.ptr
  }
}

unsafe impl<'a, T> DerefMove for MoveRef<'a, T> {
  type Uninit = MoveRef<'a, MaybeUninit<T>>;

  #[inline]
  fn deinit(self) -> Self::Uninit {
    MoveRef {
      ptr: unsafe { &mut *(self.ptr as *mut T as *mut MaybeUninit<T>) },
    }
  }

  #[inline]
  unsafe fn deref_move(this: &mut Self::Uninit) -> MoveRef<Self::Target> {
    MoveRef::new_unchecked(
      &mut *(this.ptr as *mut MaybeUninit<T> as *mut T),
    )
  }
}

unsafe impl<'a, T> DerefMove for MoveRef<'a, [T]> {
  type Uninit = MoveRef<'a, [MaybeUninit<T>]>;

  #[inline]
  fn deinit(self) -> Self::Uninit {
    MoveRef {
      ptr: unsafe { &mut *(self.ptr as *mut [T] as *mut [MaybeUninit<T>]) },
    }
  }

  #[inline]
  unsafe fn deref_move(this: &mut Self::Uninit) -> MoveRef<Self::Target> {
    MoveRef::new_unchecked(
      &mut *(this.ptr as *mut [MaybeUninit<T>] as *mut [T]),
    )
  }
}

impl<T: ?Sized> Drop for MoveRef<'_, T> {
  #[inline]
  fn drop(&mut self) {
    unsafe { ptr::drop_in_place(self.ptr) }
  }
}

impl<'a, T> From<MoveRef<'a, T>> for Pin<MoveRef<'a, T>> {
  #[inline]
  fn from(x: MoveRef<'a, T>) -> Self {
    MoveRef::into_pin(x)
  }
}

/// Moving dereference operations.
///
/// This trait is the `&move` analogue of [`Deref`], for taking a pointer that
/// is the *sole owner* its pointee and converting it to a [`MoveRef`]. In
/// particular, a pointer type `P` owns its contents if dropping it would cause
/// its pointee's destructor to run.
///
/// For example:
/// - [`MoveRef<T>`] implements `DerefMove` by definition.
/// - [`Box<T>`] implements `DerefMove`, since it drops the `T` in its
///   destructor.
/// - [`&mut T`] does *not* implement `DerefMove`, because it is
///   necessarily a borrow of a longer-lived, "truly owning" reference.
/// - [`Rc<T>`] and [`Arc<T>`] do *not* implement `DerefMove`, because even
///   though they own their pointees, they are not the *sole* owners. Dropping
///   a reference-counted pointer need not run the destructor if other pointers
///   are still alive.
/// - [`Pin<P>`] for `P: DerefMove` implements `DerefMove` only when
///   `P::Target: Unpin`, since `DerefMove: DerefMut`. To 
///
/// # Principle of Operation
/// 
/// Unfortunately, because we don't yet have language support for `&move`, we
/// need to break the implementation into two steps:
/// - Inhibit the "inner destructor" of the pointee, so that the smart pointer
///   is now managing dumb bytes. This is usually accomplished by converting the
///   pointee type to [`MaybeUninit<T>`].
/// - Extract a [`MoveRef`] out of the "deinitialized" pointer.
/// 
/// The first part is used to root the storage to the stack in such a way that
/// the putative `MoveRef` can run the destructor without a double-free
/// occurring. The second part needs to be separate, since the `MoveRef`
/// derives its lifetime from this "rooted" storage.
/// 
/// The correct way to perform a `DerefMove` operation is thus:
/// ```
/// # use moveit::{move_ref::{DerefMove, MoveRef}, slot::Slot};
/// # slot!(x: i32);
/// # let p = slot.put(5);
/// # type MyPtr<'a> = MoveRef<'a, i32>;
/// let mut deinit = MyPtr::deinit(p);
/// let move_ref = unsafe { MyPtr::deref_move(&mut deinit) };
/// ```
///
/// The [`move_ref!()`]` macro can do this safely in a single operation.
///
/// # Safety
///
/// Implementing `DerefMove` correctly requires that the uniqueness requirement
/// described above is upheld. In particular, the following function *must not*
/// violate memory safety:
/// ```
/// # use moveit::move_it::{DerefMove, move_ref, MoveRef};
/// fn move_out_of<P>(p: P) -> P::Target
/// where
///   P: DerefMove,
///   P::Target: Sized,
/// {
///   unsafe {
///     // Replace `p` with a move reference into it.
///     move_ref!(p);
///     
///     // Move out of `p`. From this point on, the `P::Target` destructor must
///     // run when, and only when, the function's return value goes out of
///     // scope per the usual Rust rules.
///     //
///     // In particular, the original `p` or any pointer it came from must not
///     // run the destructor when they go out of scope, under any circumstance.
///     MoveRef::into_inner(p)
///   }
/// }
/// ```
/// 
/// This criterion is key to the implementation of `deinit`, which will usually
/// transmute the pointer in some manner.
pub unsafe trait DerefMove: DerefMut + Sized {
  /// An "uninitialized" version of `Self`.
  /// 
  /// This is usually `Self` but with `Target` changed to
  /// `MaybeUninit<Self::Target>`.
  type Uninit: Sized;

  /// "Deinitializes" `self`, producing an opaque type that will destroy the
  /// storage of `*self` without calling the pointee destructor.
  fn deinit(self) -> Self::Uninit;

  /// Moves out of `this`, producing a [`MoveRef`] that owns its contents.
  /// 
  /// # Safety
  /// 
  /// This function may only be called on a value obtained from
  /// [`DerefMove::deinit()`], and it may only be called *once* on it. Failure
  /// to do so may result in double-frees.
  /// 
  /// In other words, every call to `deref_move()` must be matched up to exactly
  /// one call to `deinit()`.
  unsafe fn deref_move(this: &mut Self::Uninit) -> MoveRef<Self::Target>;
}

unsafe impl<P> DerefMove for Pin<P>
where
  P: DerefMove,
  P::Uninit: Deref, // Required due to a bound on Pin::new_unchecked().
  P::Target: Unpin,
{
  type Uninit = Pin<P::Uninit>;

  fn deinit(self) -> Self::Uninit {
    unsafe {
      Pin::new_unchecked(Pin::into_inner_unchecked(self).deinit())
    }
  }

  /// Moves out of `this`, producing a [`MoveRef`] that owns its contents.
  /// 
  /// # Safety
  /// 
  /// This function may only be called on a value obtained from
  /// [`DerefMove::deinit()`], and it may only be called *once* on it. Failure
  /// to do so may result in double-frees.
  /// 
  /// In other words, every call to `deref_move()` must be matched up to exactly
  /// one call to `deinit()`.
  unsafe fn deref_move(this: &mut Self::Uninit) -> MoveRef<Self::Target> {
    P::deref_move(&mut *(this as *mut Self::Uninit as *mut P::Uninit))
  }
}

pub trait PinExt<P: DerefMove> {
  fn as_move(this: MoveRef<Pin<P>>) -> Pin<MoveRef<P::Target>>;
}

impl<P: DerefMove> PinExt<P> for Pin<P> {
  fn as_move(this: MoveRef<Pin<P>>) -> Pin<MoveRef<P::Target>> {
    todo!()
  }
}

#[doc(hidden)]
pub mod __macro {
  use core::marker::PhantomData;
  use super::*;

  /// Type-inference helper for `move_ref!`.
  pub struct DerefPhantom<T>(PhantomData<*const T>);
  impl<T: DerefMove> DerefPhantom<T> {
    #[inline]
    pub fn new(_: &T) -> Self {
      Self(PhantomData)
    }

    #[inline]
    pub unsafe fn deref_move(self, this: &mut T::Uninit) -> MoveRef<T::Target> {
      T::deref_move(this)
    }
  }
}

/// Performs a move-dereference operation.
/// 
/// If [`MoveRef`] is a library implementation of the `&move T`, this macro is
/// the equivalent of the `&move expr` operator.
/// 
/// Unfortunately, this macro cannot be an expression, since it must introduce
/// `let` bindings in the scope of `$name`. Instead, it takes the name of an
/// existing binding and shadows it with the resulting [`MoveRef`]. For
/// example:
/// 
/// ```
/// # use moveit::move_ref;
/// let p = Box::new(5);
/// move_ref!(p); // `p` now has type `MoveRef<'_, i32>`. 
/// ```
#[macro_export]
macro_rules! move_ref {
  ($($name:ident),* $(,)?) => {$(
    let ph = $crate::move_ref::__macro::DerefPhantom::new(&$name);
    let mut $name = $crate::move_ref::DerefMove::deinit($name);

    #[allow(unused_mut)]
    let mut $name = ph.deref_move(&mut $name);
  )*};
}
