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

//! Slice types to use with `moveit::Vec`.

use core::marker::Unpin;
use core::mem;
use core::mem::MaybeUninit;
use core::ops::Bound;
use core::ops::Deref;
use core::ops::DerefMut;
use core::ops::RangeBounds;
use core::pin::Pin;
use core::ptr;
use core::slice;

use crate::drop_flag::DropFlag;
use crate::drop_flag::QuietFlag;
use crate::move_ref::MoveRef;
use crate::new::MoveNew;
use crate::new::New;
use crate::new::Swap;

#[cfg(doc)]
use super::std;

/// A dynamically-sized view into a contiguous sequence, compatible with
/// [`New`]-using types.
///
/// Unlike an ordinary Rust slice, the contents of a `&Slice<T>` or
/// `&mut Slice<T>` are considered pinned; they should be viewed as thin
/// wrappers over `Pin<&[T]>` and `Pin<&mut [T]>`, respectively.
///
/// Compare [`[T]`].
#[repr(transparent)]
pub struct Slice<T> {
  inner: [T],
}

impl<T> Slice<T> {
  const ZST: bool = mem::size_of::<T>() == 0;

  /// Forms a slice from a pointer and a length.
  ///
  /// Compare: [`std::slice::from_raw_parts()`].
  ///
  /// # Safety
  ///
  /// This function has the same contract as the following `unsafe` function,
  /// formed as the composition of two `unsafe` functions:
  /// ```
  /// # use core::{slice, pin::Pin};
  /// unsafe fn pinned_from_raw_parts<'a>(ptr: *const T, len: usize) -> Pin<&'a [T]> {
  ///   Pin::new_unchecked(slice::from_raw_parts(ptr, len))
  /// }
  /// ```
  pub unsafe fn from_raw_parts<'a>(ptr: *const T, len: usize) -> &'a Self {
    mem::transmute(slice::from_raw_parts(ptr, len))
  }

  /// Forms a mutable slice from a pointer and a length.
  ///
  /// Compare: [`std::slice::from_raw_parts_mut()`].
  ///
  /// # Safety
  ///
  /// This function has the same contract as the following `unsafe` function:
  /// ```
  /// # use core::{slice, pin::Pin};
  /// unsafe fn pinned_from_raw_parts_mut<'a>(ptr: *mut T, len: usize) -> Pin<&'a mut [T]> {
  ///   Pin::new_unchecked(slice::from_raw_parts_mut(ptr, len))
  /// }
  /// ```
  pub unsafe fn from_raw_parts_mut<'a>(
    ptr: *mut T,
    len: usize,
  ) -> &'a mut Self {
    mem::transmute(slice::from_raw_parts_mut(ptr, len))
  }

  /// Returns an unsafe pointer to the slice.
  ///
  /// Compare [`<[T]>::as_ptr()`].
  pub fn as_ptr(&self) -> *const T {
    self.inner.as_ptr()
  }

  /// Returns an unsafe mutable pointer to the slice.
  ///
  /// Compare [`std::Vec::as_mut_ptr()`].
  pub fn as_mut_ptr(&mut self) -> *mut T {
    self.as_ptr() as *mut T
  }

  /// Converts to a Rust language slice.
  ///
  /// Compare [`std::Vec::as_slice()`].
  pub fn as_slice(&self) -> &[T] {
    &self.inner
  }

  /// Converts to a pinned, mutable, Rust language slice.
  ///
  /// Compare [`std::Vec::as_mut_slice()`].
  pub fn as_mut_slice(&mut self) -> Pin<&mut [T]> {
    unsafe { Pin::new_unchecked(&mut self.inner) }
  }

  /// Converts to a mutable, Rust language slice.
  ///
  /// # Safety
  ///
  /// The returned slice is not pinned, even though the elements of this slice
  /// are structurally pinned. Care should be taken to not move out of the
  /// returned slice.
  pub unsafe fn as_mut_slice_unchecked(&mut self) -> &mut [T] {
    &mut self.inner
  }

  // &mut [T] polyfills. These should ideally be moved to a type such as
  // &mut moveit::Slice<T>?

  /// Returns a mutable reference to an element, if it's present at that
  /// index.
  ///
  /// Compare [`<[T]>::get_mut()`], but returns a pinned reference instead.
  pub fn get_mut<'a, R>(
    &'a mut self,
    range: R,
  ) -> Option<Pin<&'a mut <R::Output as SliceWrap>::Output>>
  where
    R: slice::SliceIndex<[T]>,
    R::Output: SliceWrap + 'a,
  {
    unsafe { Some(Pin::new_unchecked(self.inner.get_mut(range)?.wrap_mut())) }
  }

  /// Returns a mutable reference to an element, without doing bounds checking.
  ///
  /// Similar to [`<[T]>::get_unchecked_mut()`], but returns a pinned reference
  /// instead.
  ///
  /// # Safety
  ///
  /// Usual out-of-bounds access caveats apply.
  pub unsafe fn get_unchecked_mut<'a, R>(
    &'a mut self,
    range: R,
  ) -> Pin<&'a mut <R::Output as SliceWrap>::Output>
  where
    R: slice::SliceIndex<[T]>,
    R::Output: SliceWrap + 'a,
  {
    self
      .as_mut_slice()
      .map_unchecked_mut(|s| s.get_unchecked_mut(range).wrap_mut())
  }

  /// Like `get_unchecked_mut()`, but returns a reference with an unbound
  /// lifetime.
  pub(crate) unsafe fn get_unchecked_unbound_mut<'a, R>(
    &mut self,
    range: R,
  ) -> Pin<&'a mut <R::Output as SliceWrap>::Output>
  where
    R: slice::SliceIndex<[T]>,
    R::Output: SliceWrap + 'a,
  {
    let inner = Pin::into_inner_unchecked(self.get_unchecked_mut(range));
    Pin::new_unchecked(mem::transmute(inner))
  }

  /// Returns a move reference to an element, without doing bounds checking.
  ///
  /// Similar to [`<[T]>::get_unchecked_mut()`], but returns a [`MoveRef`]
  /// instead.
  ///
  /// # Safety
  ///
  /// Usual out-of-bounds access caveats apply; moreover, care should be taken
  /// not to drop the returned move reference without making sure to fix
  /// up the length of the vector, too.
  ///
  /// In general, this function makes it almost trivial to accidentally leave
  /// uninitialized memory in the vector. Very danger.
  pub unsafe fn get_unchecked_move<'a, R>(
    &'a mut self,
    range: R,
    drop_flag: DropFlag<'a>,
  ) -> Pin<MoveRef<'a, R::Output>>
  where
    R: slice::SliceIndex<[T]>,
  {
    MoveRef::into_pin(MoveRef::new_unchecked(
      Pin::into_inner_unchecked(self.get_unchecked_mut(range)),
      drop_flag,
    ))
  }

  /// Like `get_unchecked_move()`, but returns a reference with an unbound
  /// lifetime.
  pub(crate) unsafe fn get_unchecked_unbound_move<'a, R>(
    &mut self,
    range: R,
    drop_flag: DropFlag<'a>,
  ) -> Pin<MoveRef<'a, R::Output>>
  where
    R: slice::SliceIndex<[T]>,
  {
    MoveRef::into_pin(MoveRef::new_unchecked(
      Pin::into_inner_unchecked(self.get_unchecked_unbound_mut(range)),
      drop_flag,
    ))
  }

  /// Moves out of the `idx`th element to the given place.
  pub(crate) unsafe fn move_unchecked(
    &mut self,
    idx: usize,
    place: Pin<&mut MaybeUninit<T>>,
  ) where
    T: MoveNew,
  {
    // SAFETY: We don't need to set a trap, since `move_new()` is tailored to
    // the specific type and should not be rudely forgetting anything.
    let qf = QuietFlag::new();
    qf.flag().inc();

    MoveNew::move_new(self.get_unchecked_unbound_move(idx, qf.flag()), place)
  }

  /// Assigns a new value at `index` using the given [`New`].
  ///
  /// This function will destroy the element at the old location.
  ///
  /// # Panics
  ///
  /// Panics if `index` is out of bounds.
  pub fn assign(&mut self, index: usize, new: impl New<Output = T>) {
    unsafe {
      // We get a free bounds check out of this.
      let ptr = (&mut self.as_mut_slice_unchecked()[index]) as *mut T;

      // First, destroy the element at that position.
      // TODO: Not exception-safe!
      ptr::drop_in_place(ptr);

      // Then, emplace the new element.
      new.new(Pin::new_unchecked(&mut *(ptr as *mut MaybeUninit<T>)));
    }
  }

  /// Swaps two elements in the vector.
  ///
  /// Does not perform a swap when `first == second`.
  ///
  /// Compare [`<[T]>::swap()`].
  ///
  /// # Panics
  ///
  /// Panics if either `first` or `second` is out of bounds.
  pub fn swap(&mut self, first: usize, second: usize)
  where
    T: Swap,
  {
    self.bounds_check(first..);
    self.bounds_check(second..);

    unsafe {
      self.swap_unchecked(first, second);
    }
  }

  /// Swaps two elements in the vector, without doing bounds checking.
  ///
  /// Does not perform a swap when `first == second`.
  ///
  /// Compare [`<[T]>::swap_unchecked()`].
  ///
  /// # Safety
  ///
  /// The caller is responsible for ensuring both indices are in-bounds.
  pub unsafe fn swap_unchecked(&mut self, first: usize, second: usize)
  where
    T: Swap,
  {
    if Self::ZST || first == second {
      return;
    }

    let x = self.get_unchecked_unbound_mut(first);
    let y = self.get_unchecked_unbound_mut(second);
    x.swap_with(y);
  }

  /// Performs a bounds check on a range-like type, returning its start and end
  /// relative to this vector.
  #[inline]
  pub(crate) fn bounds_check(
    &self,
    range: impl RangeBounds<usize>,
  ) -> (usize, usize) {
    let start = match range.start_bound() {
      Bound::Unbounded => 0,
      Bound::Included(x) => *x,
      Bound::Excluded(_) => unreachable!(),
    };

    let end = match range.end_bound() {
      Bound::Unbounded => self.len(),
      Bound::Included(x) => *x + 1,
      Bound::Excluded(x) => *x,
    };

    if start > self.len() {
      panic!("index out of bounds: {} > {}", start, self.len())
    }

    if end > self.len() {
      panic!("index out of bounds: {} > {}", end, self.len())
    }

    (start, end)
  }
}

impl<T> Deref for Slice<T> {
  type Target = [T];
  fn deref(&self) -> &[T] {
    &self.inner
  }
}

impl<T: Unpin> DerefMut for Slice<T> {
  fn deref_mut(&mut self) -> &mut [T] {
    &mut self.inner
  }
}

#[doc(hidden)]
pub trait SliceWrap {
  type Output: ?Sized;
  unsafe fn wrap_ref(&self) -> &Self::Output;
  unsafe fn wrap_mut(&mut self) -> &mut Self::Output;
}

impl<T> SliceWrap for T {
  type Output = T;
  unsafe fn wrap_ref(&self) -> &Self::Output {
    self
  }
  unsafe fn wrap_mut(&mut self) -> &mut Self::Output {
    self
  }
}

impl<T> SliceWrap for [T] {
  type Output = Slice<T>;
  unsafe fn wrap_ref(&self) -> &Self::Output {
    mem::transmute(self)
  }
  unsafe fn wrap_mut(&mut self) -> &mut Self::Output {
    mem::transmute(self)
  }
}
