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

//! A [`New`]-friendly [`std::Vec`] analogue.
//!
//! This type is very similar to the standard library's `Vec` type, but with
//! some key differences:
//! - Functions like [`Vec::insert()`] and [`Vec::push()`] take in a [`New`]
//!   argument, rather than a value, allowing for direct construction.
//! - Almost all functions require `T: MoveNew`, since values are moved on
//!   resizing.
//! - Functions that would normally remove an element instead return a
//!   [`MoveRef<T>`], making it the caller's problem to decide what to do with
//!   it.
//!   
//! Support for truly-unmovable types isn't quite there yet.

use core::borrow::Borrow;
use core::fmt;
use core::hash;
use core::iter::FromIterator;
use core::mem;
use core::mem::MaybeUninit;
use core::ops::Deref;
use core::ops::DerefMut;
use core::ops::RangeBounds;
use core::pin::Pin;
use core::ptr;
use core::ptr::NonNull;
use core::slice;

use alloc::alloc::Layout;

use crate::drop_flag::QuietFlag;
use crate::move_ref::MoveRef;
use crate::moveit;
use crate::new;
use crate::new::CopyNew;
use crate::new::MoveNew;
use crate::new::New;
use crate::new::Swap;

#[path = "slice.rs"]
mod slices;
pub use slices::*;

#[cfg(test)]
mod test;

#[cfg(doc)]
mod std {
  pub use ::alloc::vec::Vec;
  pub use core::*;
}

/// A contiguous growable array type, compatible with [`New`]-using types.
///
/// Compare [`std::Vec`].
pub struct Vec<T> {
  ptr: NonNull<T>,
  capacity: usize,
  len: usize,

  // Scratch space for a drop flag to use inside of an iterator.
  // This does not affect synchronization, since it is only used when we
  // have a &mut Vec anyways.
  //
  // This is *not* used for trapping the overall vector! A Vec<T> owns its
  // storage and can be forgotten safely.
  drop_flag: QuietFlag,
}

// SAFETY: std::Vec<T> is Send + Sync; see comment on scratch_space above.
unsafe impl<T: Send> Send for Vec<T> {}
unsafe impl<T: Sync> Sync for Vec<T> {}

impl<T> Vec<T> {
  /// True if the element type is a ZST.
  ///
  /// This constant is used to short-circuit certain kinds of logic that don't
  /// really make sense with ZSTs, which is roughly how `Vec` works too. The
  /// following things have been changed:
  /// - Allocation always succeeds.
  /// - Capacity is infinite.
  /// - Insertion (and pushing) just increment the length.
  /// - The pointer is always dangling.
  /// - Removal always returns the same pointer value; we formulate this as
  ///   there being infinitely-many disjoint objects at the same address.
  const ZST: bool = mem::size_of::<T>() == 0;

  const MIN_CAPACITY: usize = 16;

  /// Constructs a new, empty `Vec<T>`.
  ///
  /// Compare [`std::Vec::new()`].
  pub fn new() -> Self {
    Self {
      ptr: NonNull::dangling(),
      capacity: if Self::ZST { usize::MAX } else { 0 },
      len: 0,
      drop_flag: QuietFlag::new(),
    }
  }

  /// Constructs a new, empty `Vec<T>` with the specified capacity.
  ///
  /// Compare [`std::Vec::with_capacity()`].
  ///
  /// # Panics
  ///
  /// Panics if the requested allocation size (in bytes) overflows an isize.
  pub fn with_capacity(capacity: usize) -> Self {
    if capacity == 0 || Self::ZST {
      return Self::new();
    }

    let layout =
      Layout::array::<T>(capacity).expect("overflow in layout calculation");
    let ptr = unsafe { alloc::alloc::alloc(layout) };
    assert!(!ptr.is_null(), "allocation failure");

    Self {
      ptr: unsafe { NonNull::new_unchecked(ptr as *mut T) },
      capacity,
      len: 0,
      drop_flag: QuietFlag::new(),
    }
  }

  /// Creates a `Vec<T>` using the raw components of another vector.
  ///
  /// Compare [`std::Vec::from_raw_parts()`].
  ///
  /// # Safety
  ///
  /// This function will blindly re-assemble a `Vec<T>` without thinking. The
  /// usual caveats apply.
  pub unsafe fn from_raw_parts(
    ptr: *mut T,
    length: usize,
    capacity: usize,
  ) -> Self {
    Self {
      ptr: NonNull::new_unchecked(ptr),
      len: length,
      capacity,
      drop_flag: QuietFlag::new(),
    }
  }

  /// Creates a new `Vec<T>` using the constructors returned by `iter`.
  ///
  /// Due to trait coherence issues, this cannot be exposed via `.collect()`.
  pub fn of<I, N>(iter: I) -> Self
  where
    T: MoveNew,
    I: IntoIterator<Item = N>,
    N: New<Output = T>,
  {
    let iter = iter.into_iter();
    let mut vec = Vec::with_capacity(iter.size_hint().0);
    for n in iter {
      vec.push(n);
    }
    vec
  }

  /// Unpins this vector.
  ///
  /// This function requires that the contained type be `Unpin`.
  pub fn into_unpin(mut self) -> alloc::vec::Vec<T>
  where
    T: Unpin,
  {
    let vec = unsafe {
      alloc::vec::Vec::from_raw_parts(
        self.as_mut_ptr(),
        self.len(),
        self.capacity(),
      )
    };
    mem::forget(self);
    vec
  }

  /// Returns the number of elements the vector can hold without reallocating
  /// and moving.
  ///
  /// Compare [`std::Vec::capacity()`].
  pub fn capacity(&self) -> usize {
    self.capacity
  }

  /// Reserves capacity for at least `additional` more elements.
  ///
  /// Compare [`std::Vec::reserve()`].
  ///
  /// # Panics
  ///
  /// Panics if the requested allocation size (in bytes) overflows an isize.
  pub fn reserve(&mut self, additional: usize)
  where
    T: MoveNew,
  {
    self.grow(Grow::AtLeastBy(additional))
  }

  /// Reserves capacity for at exactly `additional` more elements.
  ///
  /// Compare [`std::Vec::reserve_exact()`].
  ///
  /// # Panics
  ///
  /// Panics if the requested allocation size (in bytes) overflows an isize.
  pub fn reserve_exact(&mut self, additional: usize)
  where
    T: MoveNew,
  {
    self.grow(Grow::Exactly(additional))
  }

  /// Shrinks the capacity of the vector as much as possible.
  ///
  /// Compare [`std::Vec::shrink_to_fit()`].
  pub fn shrink_to_fit(&mut self)
  where
    T: MoveNew,
  {
    self.resize_raw(self.len())
  }

  // fn into_boxed_slice(self) -> Pin<Box<[T]>>

  /// Shortens the vector, keeping the first len elements and dropping the rest.
  ///
  /// Compare [`std::Vec::truncate()`].
  ///
  /// # Panics
  ///
  /// Panics if `len` is greater than the vector's current length.
  pub fn truncate(&mut self, len: usize) {
    self.bounds_check(len..);

    // Drop everything past `len`.
    unsafe {
      let slice = self.as_mut_slice().get_unchecked_mut();
      ptr::drop_in_place(&mut slice[len..])
    }

    self.len = len;
  }

  /// Extracts a slice containing the entire vector.
  ///
  /// Compare [`std::Vec::as_slice()`].
  pub fn as_slice(&self) -> &[T] {
    &*self
  }

  /// Extracts a pinned mutable slice of the entire vector.
  ///
  /// Compare [`std::Vec::as_mut_slice()`].
  pub fn as_mut_slice(&mut self) -> Pin<&mut [T]> {
    unsafe {
      Pin::new_unchecked(slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len))
    }
  }

  /// Forces the length of the vector to `new_len`.
  ///
  /// Compare [`std::Vec::set_len()`].
  ///
  /// # Safety
  ///
  /// `new_len` must be smaller than the capacity of the vector, and all values
  /// in the vector below the new length must be valid and initialized.
  pub unsafe fn set_len(&mut self, new_len: usize) {
    self.len = new_len;
  }

  /// Returns a constructor that moves an element out of the vector.
  ///
  /// The removed element is replaced by the last element of the vector.
  ///
  /// Compare [`std::Vec::swap_remove()`].
  pub fn swap_remove(&mut self, index: usize) -> impl New<Output = T> + '_
  where
    T: Swap + MoveNew,
  {
    unsafe {
      new::by_raw(move |place| {
        self.bounds_check(index..);

        let end = self.len() - 1;
        self.swap_unchecked(index, end);

        self.len -= 1;
        self.move_unchecked(end, place);
      })
    }
  }

  /// Emplaces an element at position `index` within the vector, moving all
  /// elements after it to the right.
  ///
  /// Compare [`std::Vec::insert()`].
  #[allow(clippy::branches_sharing_code)]
  pub fn insert(&mut self, index: usize, element: impl New<Output = T>)
  where
    T: MoveNew,
  {
    self.bounds_check(..index);
    if index == self.len() || Self::ZST {
      self.push(element);
      return;
    }

    let new_len = self.len() + 1;

    // insert() is a little weird because to minimize moves we need to do the
    // grow operation manually. Thankfully this is the only vector operation
    // that requires doing this.

    let new_cap = Grow::AtLeastBy(1)
      .new_cap(self.len(), self.capacity())
      .expect("overflow in layout calculation");
    if new_cap != 0 {
      // If we need to reallocate, insert the element as we're copying all the
      // other elements.
      moveit! {
        let old = &move mem::replace(self, Self::with_capacity(new_cap));
      }

      for (i, val) in old.into_iter().enumerate() {
        unsafe {
          if i < index {
            MoveNew::move_new(val, self.slot(i));
          } else {
            MoveNew::move_new(val, self.slot(i + 1));
          }
        }
      }
      unsafe {
        element.new(self.slot(index));
      }
    } else {
      // Otherwise, do a bunch of moves, starting from the back and going all
      // the way to the front.
      // TODO(mcyoung): Optimize by calling assignment, once that's added.
      for i in (index..self.len()).rev() {
        unsafe {
          // SAFETY: We don't need to set a trap, since `move_new()` is tailored to
          // the specific type and should not be rudely forgetting anything.
          let qf = QuietFlag::new();
          qf.flag().inc();
          let src = self.get_unchecked_unbound_move(i, qf.flag());
          let dest = self.slot(i + 1);
          MoveNew::move_new(src, dest);
        }
      }
      unsafe {
        element.new(self.slot(index));
      }
    }
    self.len = new_len;
  }

  /// Removes and returns a reference to an element at position `index` within
  /// the vector, moving all elements after it to the left.
  ///
  /// Compare [`std::Vec::remove()`].
  pub fn remove(&mut self, index: usize) -> impl New<Output = T> + '_
  where
    T: Swap + MoveNew,
  {
    unsafe {
      new::by_raw(move |place| {
        self.bounds_check(index..);

        // This is less tricky than `insert`, since we only need to rotate the range
        // index..self.len(). We do this by swapping every adjacent pair in the
        // range.
        for i in index..self.len() - 1 {
          self.swap_unchecked(i, i + 1);
        }

        // The removed element winds up at the very end, so we just pop the vector.
        self.len -= 1;
        let end = self.len;
        self.move_unchecked(end, place);
      })
    }
  }

  // fn retain<F>(&mut self, f: F)

  /// Appends an element to the back of the collection, emplaced directly from
  /// a `New`.
  ///
  /// Compare [`std::Vec::push()`].
  pub fn push(&mut self, value: impl New<Output = T>)
  where
    T: MoveNew,
  {
    self.grow(Grow::AtLeastBy(1));
    unsafe {
      value.new(self.slot(self.len()));
      self.len += 1;
    }
  }

  /// Removes the last element from a vector and returns a reference to it,
  /// or `None` if it is empty.
  ///
  /// Compare [`std::Vec::pop()`].
  pub fn pop(&mut self) -> Option<impl New<Output = T> + '_>
  where
    T: MoveNew,
  {
    if self.is_empty() {
      return None;
    }
    unsafe {
      Some(new::by_raw(move |place| {
        self.len -= 1;
        let end = self.len;
        self.move_unchecked(end, place);
      }))
    }
  }

  /// Moves all the elements of other into Self, leaving other empty.
  ///
  /// Compare [`std::Vec::append()`].
  pub fn append(&mut self, other: &mut Vec<T>)
  where
    T: MoveNew,
  {
    self.reserve(other.len());
    for val in other.drain(..) {
      self.push(new::mov(val))
    }
  }

  /// Creates a draining iterator that removes the specified range and yields
  /// the returned items.
  ///
  /// If the returned iterator is [`mem::forget`]'d, the allocation this vector
  /// pointed to is leaked forever, and `self` is replaced with a fresh,
  /// empty vector.
  ///
  /// Compare [`std::Vec::drain()`].
  ///
  /// # Panics
  ///
  /// Panics if `range` is out of bounds.
  pub fn drain<R>(&mut self, range: R) -> Drain<T>
  where
    T: MoveNew,
    R: RangeBounds<usize>,
  {
    let mut vec = mem::take(self);
    let (start, end) = vec.bounds_check(range);
    let range_len = end.saturating_sub(start);
    let full_len = vec.len;

    vec.len = start;
    Drain {
      tail_start: start + range_len,
      tail_len: full_len - (start + range_len),
      index: start,
      vec,
      place: self,
    }
  }

  /// Clears the vector, removing all values.
  ///
  /// Compare [`std::Vec::clear()`].
  pub fn clear(&mut self) {
    self.truncate(0)
  }

  /// Splits the vector into two at the given index.
  ///
  /// Returns a newly allocated vector containing all elements after `at`;
  /// `self` will be left with the remaining elements but otherwise unchanged.
  ///
  /// Compare [`std::Vec::split_off()`].
  ///
  /// # Panics
  ///
  /// Panics if `at` is out of bounds.
  pub fn split_off(&mut self, at: usize) -> Self
  where
    T: MoveNew,
  {
    if at == 0 {
      return mem::take(self);
    }

    if at == self.len() {
      return Vec::new();
    }

    self.drain(at..).collect()
  }

  /// Resizes the vector in-place, so that `len` becomes `new_len`.
  ///
  /// If `new_len` is greater than `len`, `f` is used to generate [`New`]s for
  /// filling the new slots. The return values of `f` end up in the vector in
  /// the order they were generated.
  ///
  /// Otherwise, this function truncates `self`.
  ///
  /// See [`Vec::resize()`]; compare [`std::Vec::resize_with()`].
  pub fn resize_with<F, N>(&mut self, new_len: usize, mut f: F)
  where
    T: MoveNew,
    F: FnMut() -> N,
    N: New<Output = T>,
  {
    if new_len == self.len() {
      return;
    }

    if new_len < self.len() {
      self.truncate(new_len);
      return;
    }

    self.reserve(new_len - self.len());
    for i in self.len()..new_len {
      unsafe {
        f().new(self.slot(i));
      }
    }
  }

  /// Consumes and leaks the vector, returning a pinned mutable reference to its
  /// contents.
  ///
  /// This function is mainly useful for data that lives for the remainder of
  /// the program’s life. Dropping the returned reference will cause a memory
  /// leak.
  ///
  /// Compare [`std::Vec::leak()`].
  pub fn leak<'a>(mut self) -> Pin<&'a mut [T]> {
    let slice = unsafe {
      // Extend the lifetime to unlink this slice from `self`.
      mem::transmute::<_, Pin<&'a mut [T]>>(self.as_mut_slice())
    };
    mem::forget(self);
    slice
  }

  /// Resizes the vector in-place, so that `len` becomes `new_len`.
  ///
  /// If `new_len` is greater than `len`, `value` is `new::copy`'d to fill new
  /// slots as necessary.
  ///
  /// Otherwise, this function truncates `self`.
  ///
  /// Compare [`std::Vec::resize()`].
  pub fn resize<F, N>(&mut self, new_len: usize, value: impl New<Output = T>)
  where
    T: MoveNew + CopyNew,
  {
    if new_len == self.len() {
      return;
    }

    if new_len < self.len() {
      self.truncate(new_len);
      return;
    }

    self.reserve(new_len - self.len());
    self.push(value);

    unsafe {
      let value = self.get_unchecked(self.len() - 1);
      for i in self.len()..new_len {
        CopyNew::copy_new(value, self.slot(i))
      }
    }
  }

  /// Clones and appends all elements in `other` to the vector.
  ///
  /// Compare [`std::Vec::extend_from_slice()`].
  pub fn extend_from_slice(&mut self, other: &[T])
  where
    T: MoveNew + CopyNew,
  {
    self.reserve(other.len());
    for x in other {
      self.push(new::copy(x));
    }
  }
}

/// A vector growth request.
enum Grow {
  /// Ensure that there are exactly `n` empty slots in the vector.
  Exactly(usize),
  /// Ensure that there are at least `n` empty slots in the vector, preferring
  /// to grow to the next power of two.
  AtLeastBy(usize),
}

impl Grow {
  /// Returns the new capacity of a vector with the given length and capacity,
  /// relative to this growth request.
  ///
  /// Returns `None` on overflow, and returns `Some(0)` if no growth should
  /// occur at all.
  fn new_cap(self, old_len: usize, old_cap: usize) -> Option<usize> {
    let available = old_cap.checked_sub(old_len)?;
    let val = match self {
      Self::Exactly(n) if n > available => old_len.checked_add(n)?,
      Self::AtLeastBy(n) if n > available => {
        old_len.checked_add(n)?.checked_next_power_of_two()?
      }
      _ => return Some(0),
    };

    Some(val.max(Vec::<()>::MIN_CAPACITY))
  }
}

impl<T: MoveNew> Vec<T> {
  /// Gets an empty slot at `idx`. Takes `&self` and performs no bounds checks,
  /// so beware aliasing.
  unsafe fn slot(&self, idx: usize) -> Pin<&mut MaybeUninit<T>> {
    Pin::new_unchecked(
      &mut *self.ptr.as_ptr().add(idx).cast::<MaybeUninit<T>>(),
    )
  }

  /// Grows `self` by the given growth request.
  fn grow(&mut self, grow: Grow) {
    if Self::ZST {
      return;
    }

    let new_cap = grow.new_cap(self.len(), self.capacity());
    if let Some(0) = new_cap {
      return;
    }

    self.resize_raw(new_cap.expect("overflow in layout calculation"))
  }

  /// Resizes `self` directly to exactly `new_cap`.
  ///
  /// This function can be used to implement both buffer growth and truncation.
  fn resize_raw(&mut self, new_cap: usize) {
    if Self::ZST {
      return;
    }

    // Request a new allocation with the requested cap, replacing
    // `self` with it.
    moveit! {
      let old = &move mem::replace(self, Self::with_capacity(new_cap));
    }

    // Find the new length: it will be `old`'s length if this is growth, and
    // the new capacity if it is shrinking.
    let len = old.len().min(new_cap);

    // Move the relevant prefix of `old` into `self`. The rest of `old` will
    // be dropped when the iterator is dropped.
    for (i, val) in old.into_iter().enumerate().take(len) {
      unsafe {
        MoveNew::move_new(val, self.slot(i));
      }
    }

    // Set the length of the new `self` to the correct value.
    self.len = len
  }
}

// "Load bearing" trait impls.

impl<T> Deref for Vec<T> {
  type Target = Slice<T>;
  fn deref(&self) -> &Slice<T> {
    unsafe { Slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
  }
}

impl<T> DerefMut for Vec<T> {
  fn deref_mut(&mut self) -> &mut Slice<T> {
    unsafe { Slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) }
  }
}

impl<T> Drop for Vec<T> {
  fn drop(&mut self) {
    if self.drop_flag.flag().is_dead() {
      self.truncate(0);
      if !Self::ZST && self.capacity > 0 {
        unsafe {
          alloc::alloc::dealloc(
            self.ptr.as_ptr() as *mut u8,
            Layout::array::<T>(self.capacity).unwrap(),
          );
        }
      }
    }
  }
}

// "QOL" trait impls.

impl<T> AsRef<[T]> for Vec<T> {
  fn as_ref(&self) -> &[T] {
    self.as_slice()
  }
}

impl<T> Borrow<[T]> for Vec<T> {
  fn borrow(&self) -> &[T] {
    self.as_slice()
  }
}

impl<T: MoveNew + CopyNew> Clone for Vec<T> {
  fn clone(&self) -> Self {
    self.as_slice().into()
  }
}

impl<T: fmt::Debug> fmt::Debug for Vec<T> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.as_slice().fmt(f)
  }
}

impl<T> Default for Vec<T> {
  fn default() -> Self {
    Self::new()
  }
}

impl<T, U: ?Sized> PartialEq<U> for Vec<T>
where
  U: PartialEq<[T]>,
{
  fn eq(&self, other: &U) -> bool {
    PartialEq::eq(other, self.as_slice())
  }
}

impl<T: Eq> Eq for Vec<T> {}

impl<T> hash::Hash for Vec<T>
where
  T: hash::Hash,
{
  fn hash<H>(&self, state: &mut H)
  where
    H: hash::Hasher,
  {
    self.as_slice().hash(state)
  }
}

impl<T, U: ?Sized> PartialOrd<U> for Vec<T>
where
  U: PartialOrd<[T]>,
{
  fn partial_cmp(&self, other: &U) -> Option<core::cmp::Ordering> {
    PartialOrd::partial_cmp(other, self.as_slice()).map(|o| o.reverse())
  }
}

impl<T: Ord> Ord for Vec<T> {
  fn cmp(&self, other: &Self) -> core::cmp::Ordering {
    Ord::cmp(self.as_slice(), other.as_slice())
  }
}

impl<T: MoveNew + CopyNew> From<&[T]> for Vec<T> {
  fn from(slice: &[T]) -> Self {
    Self::of(slice.iter().map(new::copy))
  }
}

impl<T: MoveNew + CopyNew> From<&mut [T]> for Vec<T> {
  fn from(slice: &mut [T]) -> Self {
    slice.as_ref().into()
  }
}

impl<T: MoveNew + CopyNew, const N: usize> From<[T; N]> for Vec<T> {
  fn from(slice: [T; N]) -> Self {
    slice.as_ref().into()
  }
}

// Iterator stuff.

/// An iterator that moves out of a vector.
pub struct IntoIter<'a, T> {
  vec: &'a mut Vec<T>,
  start: *mut T,
  end: *mut T,
}

impl<T> IntoIter<'_, T> {
  /// Returns the remaining items in the iterator as a slice.
  pub fn as_slice(&self) -> &[T] {
    unsafe {
      slice::from_raw_parts(
        self.start,
        self.end.offset_from(self.start) as usize,
      )
    }
  }

  /// Returns the remaining items in the iterator as a mutable slice.
  pub fn as_mut_slice(&mut self) -> &mut [T] {
    unsafe {
      slice::from_raw_parts_mut(
        self.start,
        self.end.offset_from(self.start) as usize,
      )
    }
  }
}

impl<'a, T> Iterator for IntoIter<'a, T> {
  type Item = Pin<MoveRef<'a, T>>;
  fn next(&mut self) -> Option<Self::Item> {
    if self.start == self.end {
      return None;
    }

    let flag = unsafe { self.vec.drop_flag.flag().longer_lifetime() };
    flag.inc();

    let this = self.start;
    unsafe {
      self.start = self.start.add(1);
      // SAFETY: If this MoveRef is forgotten, then:
      // - If this function is called again, we crash.
      // - If the iterator is dropped, we crash.
      // - If the iterator is forgotten, the storage is leaked so we're ok.
      Some(MoveRef::into_pin(MoveRef::new_unchecked(&mut *this, flag)))
    }
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    let bound = self.as_slice().len();
    (bound, Some(bound))
  }

  // TODO(mcyoung): Implement more functions for optimization.
}

impl<'a, T> IntoIterator for MoveRef<'a, Vec<T>> {
  type Item = Pin<MoveRef<'a, T>>;
  type IntoIter = IntoIter<'a, T>;

  fn into_iter(mut self) -> IntoIter<'a, T> {
    let vec: &mut Vec<T> = unsafe { &mut *MoveRef::as_mut_ptr(&mut self) };
    let core::ops::Range { start, end } = vec.as_ptr_range();

    unsafe {
      vec.set_len(0);
      let _ = self.cast::<()>();
    }

    IntoIter {
      vec,
      start: start as *mut _,
      end: end as *mut _,
    }
  }
}

impl<T> Drop for IntoIter<'_, T> {
  fn drop(&mut self) {
    unsafe {
      ptr::drop_in_place(self.as_mut_slice());
      ptr::drop_in_place(self.vec);
    }
  }
}

impl<'a, T: MoveNew + 'a> FromIterator<Pin<MoveRef<'a, T>>> for Vec<T> {
  fn from_iter<I>(iter: I) -> Self
  where
    I: IntoIterator<Item = Pin<MoveRef<'a, T>>>,
  {
    let mut new = Vec::new();
    new.extend(iter);
    new
  }
}

impl<'a, T: MoveNew + 'a> FromIterator<MoveRef<'a, T>> for Vec<T> {
  fn from_iter<I>(iter: I) -> Self
  where
    I: IntoIterator<Item = MoveRef<'a, T>>,
  {
    let mut new = Vec::new();
    new.extend(iter);
    new
  }
}

impl<T: MoveNew> FromIterator<T> for Vec<T> {
  fn from_iter<I>(iter: I) -> Self
  where
    I: IntoIterator<Item = T>,
  {
    let mut new = Vec::new();
    new.extend(iter);
    new
  }
}

impl<'a, T: MoveNew + 'a> Extend<Pin<MoveRef<'a, T>>> for Vec<T> {
  fn extend<I>(&mut self, iter: I)
  where
    I: IntoIterator<Item = Pin<MoveRef<'a, T>>>,
  {
    let iter = iter.into_iter();
    self.reserve(iter.size_hint().0);
    for val in iter {
      self.push(new::mov(val));
    }
  }
}

impl<'a, T: MoveNew + 'a> Extend<MoveRef<'a, T>> for Vec<T> {
  fn extend<I>(&mut self, iter: I)
  where
    I: IntoIterator<Item = MoveRef<'a, T>>,
  {
    let iter = iter.into_iter();
    self.reserve(iter.size_hint().0);
    for val in iter {
      self.push(new::mov(val));
    }
  }
}

impl<'a, T: MoveNew + CopyNew + 'a> Extend<&'a T> for Vec<T> {
  fn extend<I>(&mut self, iter: I)
  where
    I: IntoIterator<Item = &'a T>,
  {
    let iter = iter.into_iter();
    self.reserve(iter.size_hint().0);
    for val in iter {
      self.push(new::copy(val));
    }
  }
}

impl<T: MoveNew> Extend<T> for Vec<T> {
  fn extend<I>(&mut self, iter: I)
  where
    I: IntoIterator<Item = T>,
  {
    let iter = iter.into_iter();
    self.reserve(iter.size_hint().0);
    for val in iter {
      self.push(new::of(val));
    }
  }
}

/// An iterator that moves out of a vector.
///
/// See [`Vec::drain()`].
pub struct Drain<'a, T: MoveNew> {
  // The index of the start of the "tail"; whatever is past the section of the
  // vector that we're not currently draining.
  tail_start: usize,
  // The length of the tail.
  tail_len: usize,

  // The next item we intend to yield; must be `<= tail_start`.
  index: usize,

  // The *actual* vector being drained.
  vec: Vec<T>,

  // This is where the vector we're draining from *was*, which we've
  // temporarily swapped with `vec`.
  place: &'a mut Vec<T>,
}

impl<T: MoveNew> Drain<'_, T> {
  /// Returns the remaining undrained items as a slice.
  pub fn as_slice(&self) -> &[T] {
    unsafe {
      slice::from_raw_parts(
        self.vec.as_ptr().add(self.index),
        self.tail_start - self.index,
      )
    }
  }
}

impl<'a, T: MoveNew> Iterator for Drain<'a, T> {
  type Item = Pin<MoveRef<'a, T>>;

  fn next(&mut self) -> Option<Pin<MoveRef<'a, T>>> {
    if self.index >= self.tail_start {
      return None;
    }

    let i = self.index;
    self.index += 1;
    unsafe {
      let flag = self.vec.drop_flag.flag().longer_lifetime();
      // Lengthen the lifetime to avoid capturing the &'_ self lifetime.
      Some(mem::transmute::<_, Pin<MoveRef<T>>>(
        self.vec.get_unchecked_unbound_move(i, flag),
      ))
    }
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    let bound = self.as_slice().len();
    (bound, Some(bound))
  }
}

impl<T: MoveNew> Drop for Drain<'_, T> {
  fn drop(&mut self) {
    if !self.vec.drop_flag.flag().is_dead() {
      // We've been bamboozled; no allocation re-use for you!
      return;
    }

    unsafe {
      ptr::drop_in_place(self.as_slice() as *const [T] as *mut [T]);
    }

    // Move all the remaining elements back into place, and update the length
    // back to normal.
    let start = self.vec.len();
    if start != self.tail_start {
      for i in 0..self.tail_len {
        unsafe {
          // SAFETY: We don't need to set a trap, since `move_new()` is tailored to
          // the specific type and should not be rudely forgetting anything.
          let qf = QuietFlag::new();
          let src = self
            .vec
            .get_unchecked_unbound_move(i + self.tail_start, qf.flag());
          let dst = self.vec.slot(i + start);
          MoveNew::move_new(src, dst);
        }
      }
    }

    unsafe { self.vec.set_len(start + self.tail_len) }

    // Put the vector back in its place.
    mem::swap(self.place, &mut self.vec);
  }
}
