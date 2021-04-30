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

//! Unique-owner utilities.

use core::mem;
use core::ops::Deref;
use core::ops::DerefMut;
use core::pin::Pin;

#[cfg(doc)]
use {
  crate::stackbox::StackBox,
  alloc::{boxed::Box, rc::Rc, sync::Arc},
  core as std,
};

/// A wraper-like type that can be destroyed without dropping its contents.
///
/// For example, `Box<T>`'s `OuterDrop` implementation will free the heap
/// pointer without calling `T::drop()`. The `T` it contained is now
/// uninitialized, but any resources it held (such as its own heap allocations)
/// live on.
///
/// # Safety
///
/// [`OuterDrop::outer_drop()`] must not call the inner destructor; callers may
/// assume that dropping the pointee in place, and then calling this function,
/// will not double-drop the pointee.
pub unsafe trait OuterDrop {
  /// Destroys the storage of `*this` without dropping the pointee.
  ///
  /// # Safety
  ///
  /// `this` must point to valid memory, though the pointed-to wrapper
  /// may point to uninitialized data.
  ///
  /// After calling this function, `*this` should not be dropped, but rather
  /// passed into [`std::mem::forget()`].
  unsafe fn outer_drop(this: *mut Self);
}

/// Moving dereference operations.
///
/// A type which implements `DerefMove` is the *sole owner* is its pointee; that
/// is, if `P: DerefMove`, and `p: P` is in-scope, then once `p` goes out of
/// scope, `*p` will become unreachable for the remainder of the program.
///
/// For example:
/// - [`Box<T>`] implements `DerefMove`, almost by definition.
/// - [`StackBox<T>`] implements `DerefMove`, again by definition.
/// - [`&mut T`] does *not* implement `DerefMove`, because it is
///   necessarilly a borrow of a longer-lived, "trully owning" reference.
/// - [`Rc<T>`] and [`Arc<T>`] do *not* implement `DerefMove`, because even
///   though they own their pointees, they are not the *sole* owners.
/// - [`Pin<P>`] for `P: DerefMove` implements `DerefMove` only when
///   `P::Target: Unpin`, since `DerefMove: DerefMut`.
///
/// # Safety
///
/// Implementing this safe requires that the uniqueness requirement described
/// above is upheld; in particular, the following function *must not* violate
/// memory safety:
/// ```
/// # use moveit::unique::{DerefMove, OuterDrop};
/// fn move_out_of<P>(mut p: P) -> P::Target
/// where
///   P: DerefMove,
///   P::Target: Sized,
/// {
///   unsafe {
///     // Copy the pointee out of `p`.
///     let val = (&mut *p as *mut P::Target).read();
///     
///     // Destroy `p`'s storage without running the pointee's
///     // destructor.
///     let ptr = &mut p as *mut P;
///     std::mem::forget(p);
///     P::outer_drop(ptr);
///     
///     // Return the moved pointee.
///     val
///   }
/// }
/// ```
pub unsafe trait DerefMove: DerefMut + OuterDrop {}

/// An owning pointer type that may be a unique owner.
///
/// [`Arc`], for example, implements this trait.
///
/// # Safety
///
/// Not only must [`MaybeUnique::is_unique()`] be truthful (it must not return
/// `true` for non-unique pointers), once it returns `true`, it must continue
/// to return `true` until a function is called directly on it that isn't one
/// of the following:
/// - [`MaybeUnique::is_unique()`]
/// - [`Deref::deref()`]
/// - [`DerefMut::deref_mut()`]
/// - [`OuterDrop::outer_drop()`]
///
/// Furthermore, [`MaybeUnique::is_unique()`] must not move out of the contents
/// of `self`; it must assume that `self` was unsafely produced from pinned
/// memory.
///
/// See [`Unique`].
pub unsafe trait MaybeUnique {
  /// Returns true if `self` is the unique owner of its pointee.
  fn is_unique(&self) -> bool;
}

/*
// SAFETY: By definition.
// Requires specialization because Pin<_> is #[fundamental].
unsafe impl<P: DerefMove> MaybeUnique for P {
  fn is_unique(&self) -> bool { true }
}
*/

#[allow(clippy::transmute_ptr_to_ptr)]
unsafe impl<P: MaybeUnique> MaybeUnique for Pin<P> {
  fn is_unique(&self) -> bool {
    // SAFETY: Pin<P> is repr(transparent), and the no-unpin guarantees of
    // `MaybeUnique` make this safe.
    let p: &P = unsafe { mem::transmute(self) };
    p.is_unique()
  }
}

/// An error indicating that the uniqueness check of [`Unique::new()`] failed.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NotUnique<P>(pub P);

/// An owning pointer that is guaranteed to unique, which might otherwise not
/// be, such as an [`Arc`].
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Unique<P>(P);

impl<P> Unique<P> {
  /// Tautalogically creates a new `Unique` from a uniquely-owning `p`.
  #[inline]
  pub fn new(p: P) -> Self
  where
    P: DerefMove,
  {
    Self(p)
  }

  /// Tries to create a new `Unique`, succeding if `p` is unique.
  #[inline]
  pub fn try_new(p: P) -> Result<Self, NotUnique<P>>
  where
    P: MaybeUnique,
  {
    if !p.is_unique() {
      return Err(NotUnique(p));
    }
    Ok(Unique(p))
  }

  /// Creates a new `Unique` without checking uniqueness.
  ///
  /// # Safety
  ///
  /// If `P: DerefMut + OuterDrop`, the safety guarantees of [`DerefMove`] must
  /// be observed by the caller.
  #[inline]
  pub unsafe fn new_unchecked(p: P) -> Self {
    Unique(p)
  }

  /// Consumes this `Unique`, returning its contents.
  #[inline]
  pub fn into_inner(self) -> P {
    self.0
  }
}

/*
// Requires specialization.
impl<P: MaybeUnique> core::convert::TryFrom<P> for Unique<P> {
  type Error = NotUnique<P>;
  #[inline]
  fn try_from(p: P) -> Result<Self, Self::Error> {
    Self::new(p)
  }
}
*/

impl<P: Deref> Deref for Unique<P> {
  type Target = P::Target;
  #[inline]
  fn deref(&self) -> &Self::Target {
    self.0.deref()
  }
}

impl<P: DerefMut> DerefMut for Unique<P> {
  #[inline]
  fn deref_mut(&mut self) -> &mut Self::Target {
    self.0.deref_mut()
  }
}

unsafe impl<P: OuterDrop> OuterDrop for Unique<P> {
  #[inline]
  unsafe fn outer_drop(this: *mut Self) {
    // SAFETY: repr(transparent) makes this cast safe.
    P::outer_drop(this.cast::<P>())
  }
}

// SAFETY: By definition of `MaybeUnique`.
unsafe impl<P: DerefMut + OuterDrop> DerefMove for Unique<P> {}
