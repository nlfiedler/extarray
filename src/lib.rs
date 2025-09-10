//
// Copyright (c) 2025 Nathan Fiedler
//

//! An append-only (no insert or remove) growable array as described in section
//! 3 of the paper "Immediate-Access Indexing Using Space-Efficient Extensible
//! Arrays" by Alistair Moffat and Joel Mackenzie, published in 2022.
//!
//! * ACM ISBN 979-8-4007-0021-7/22/12
//! * https://doi.org/10.1145/3572960.3572984
//!
//! This data structure is meant to hold an unknown, though likely large, number
//! of elements, otherwise `Vec` would be more appropriate. An empty array will
//! have a size of around 40 bytes. The size may not be an issue, but the lookup
//! operation has a non-trivial cost, unlike `Vec`.
//!
//! # Performance
//!
//! Most operations are either constant time, log2, or sqrt of the collection
//! size. However, the lookup operation involves several calculations and as
//! such the overall performance will be worse than `Vec`. The advantage is that
//! the memory overhead will be on the order of O(√N) vs O(N).
//!
//! # Safety
//!
//! Because this data structure is allocating memory, copying bytes using
//! pointers, and de-allocating memory as needed, there are many `unsafe` blocks
//! throughout the code.

use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};
use std::fmt;
use std::ops::{Index, IndexMut};

/// The number of bits in a usize plus one to make the math in the mapping()
/// function easier.
const BEE_BASE: u32 = (8 * std::mem::size_of::<usize>() + 1) as u32;

/// The highest numbered segment for each level and the corresponding length of
/// segments for that level.
const SEGMENT_SIZES: [(usize, usize); 16] = [
    (2, 2),
    (5, 4),
    (11, 8),
    (23, 16),
    (47, 32),
    (95, 64),
    (191, 128),
    (383, 256),
    (767, 512),
    (1535, 1024),
    (3071, 2048),
    (6143, 4096),
    (12287, 8192),
    (24575, 16384),
    (49151, 32768),
    (98303, 65536),
];

/// Compute the largest segment number for which the segment length is 2^l.
///
/// From first paragraph of section 3 of the Moffat 2022 paper.
#[inline]
fn last_segment_for_l(l: usize) -> usize {
    3 * (1 << (l - 1)) - 2
}

/// Compute the length of segments for some value of l.
///
/// From first paragraph of section 3 of the Moffat 2022 paper.
#[inline]
fn segment_len_for_l(l: usize) -> usize {
    1 << l
}

/// Determine the number of slots in the given segment.
fn slots_in_segment(segment: usize) -> usize {
    for (max, len) in SEGMENT_SIZES {
        if segment < max {
            return len;
        }
    }
    panic!("overflow, segment out of bounds")
}

/// Compute the mapping from a one-dimensional array index to a two-dimensional
/// segment number and offset pair.
///
/// Algorithm 1 from the Moffat 2022 paper
#[inline]
fn mapping(v: usize) -> (usize, usize) {
    let b = if v == 0 {
        1
    } else {
        (BEE_BASE - v.leading_zeros()) >> 1
    };
    let segment = (v >> b) + (1 << (b - 1)) - 1;
    let slot = v & ((1 << b) - 1);
    (segment, slot)
}

/// Compute the capacity for an extensible array for a count and level.
///
/// Running time is log2(count)/2.
fn capacity_for_count(count: usize, level: usize) -> usize {
    let mut capacity = 0;
    if count > 0 {
        let (last_segment, _) = mapping(count - 1);
        let mut segment = 0;
        for level in 1..=level {
            let level_limit = last_segment_for_l(level);
            let segment_len = segment_len_for_l(level);
            let difference = if level_limit < last_segment {
                level_limit - segment
            } else {
                last_segment - segment
            } + 1;
            capacity += segment_len * difference;
            segment += difference;
        }
    }
    capacity
}

///
/// Append-only growable array that uses a list of progressivly larger segments
/// to avoid the allocate-and-copy that many growable data structures typically
/// employ.
///
pub struct ExtensibleArray<T> {
    // number of elements stored in the array
    count: usize,
    // the 'l' value from the Moffat 2022 paper
    level: usize,
    // dope vector, holds pointers to allocated segments
    dope: Vec<*mut T>,
}

impl<T> ExtensibleArray<T> {
    /// Return an empty extensible array with zero capacity.
    ///
    /// Note that pre-allocating capacity has no benefit with this data
    /// structure since append operations are always constant time and no
    /// reallocation and copy is ever performed.
    pub fn new() -> Self {
        Self {
            count: 0,
            level: 1,
            dope: vec![],
        }
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Panics
    ///
    /// Panics if a new segment is allocated that would exceed `isize::MAX` _bytes_.
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn push(&mut self, value: T) {
        // lookup the segment and slot
        let (segment, slot) = mapping(self.count);
        if self.dope.len() <= segment {
            // need to add another segment
            if self.dope.len() > last_segment_for_l(self.level) {
                // when the size of the dope vector (1-based) is greater than
                // the segment number of the last segment of length 2^l, then
                // increase to the next level and hence next segment length
                self.level += 1;
            }
            let segment_len = segment_len_for_l(self.level);
            // overflowing the allocator is very unlikely as the item size would
            // have to be very large (the longest segment will be 65,536 items)
            let layout = Layout::array::<T>(segment_len).expect("unexpected overflow");
            unsafe {
                let ptr = alloc(layout).cast::<T>();
                if ptr.is_null() {
                    handle_alloc_error(layout);
                }
                self.dope.push(ptr);
            }
        }

        unsafe {
            std::ptr::write(self.dope[segment].add(slot), value);
        }
        self.count += 1;
    }

    /// Appends an element if there is sufficient spare capacity, otherwise an
    /// error is returned with the element.
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn push_within_capacity(&mut self, value: T) -> Result<(), T> {
        let (segment, _slot) = mapping(self.count);
        if self.dope.len() <= segment {
            Err(value)
        } else {
            self.push(value);
            Ok(())
        }
    }

    /// Removes the last element from an array and returns it, or `None` if it
    /// is empty.
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn pop(&mut self) -> Option<T> {
        if self.count > 0 {
            self.count -= 1;
            let (segment, slot) = mapping(self.count);
            unsafe { Some((self.dope[segment].add(slot)).read()) }
        } else {
            None
        }
    }

    /// Removes and returns the last element from a vector if the predicate
    /// returns true, or None if the predicate returns false or the vector is
    /// empty (the predicate will not be called in that case).
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn pop_if(&mut self, predicate: impl FnOnce(&mut T) -> bool) -> Option<T> {
        if self.count == 0 {
            None
        } else if let Some(last) = self.get_mut(self.count - 1) {
            if predicate(last) { self.pop() } else { None }
        } else {
            None
        }
    }

    /// Return the number of elements in the array.
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn len(&self) -> usize {
        self.count
    }

    /// Returns the total number of elements the extensible array can hold
    /// without reallocating.
    ///
    /// # Time complexity
    ///
    /// log2(count)/2
    pub fn capacity(&self) -> usize {
        capacity_for_count(self.count, self.level)
    }

    /// Returns true if the array has a length of 0.
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Retrieve a reference to the element at the given offset.
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.count {
            None
        } else {
            let (segment, slot) = mapping(index);
            unsafe { (self.dope[segment].add(slot)).as_ref() }
        }
    }

    /// Returns a mutable reference to an element.
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index >= self.count {
            None
        } else {
            let (segment, slot) = mapping(index);
            unsafe { (self.dope[segment].add(slot)).as_mut() }
        }
    }

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering of the remaining elements.
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn swap_remove(&mut self, index: usize) -> T {
        if index >= self.count {
            panic!(
                "swap_remove index (is {index}) should be < len (is {})",
                self.count
            );
        }
        // retreive the value at index before overwriting
        let (segment, slot) = mapping(index);
        unsafe {
            let index_ptr = self.dope[segment].add(slot);
            let value = index_ptr.read();
            // find the pointer of the last element and copy to index pointer
            self.count -= 1;
            let (segment, slot) = mapping(self.count);
            let last_ptr = self.dope[segment].add(slot);
            std::ptr::copy(last_ptr, index_ptr, 1);
            value
        }
    }

    /// Returns an iterator over the extensible array.
    ///
    /// The iterator yields all items from start to end.
    pub fn iter(&self) -> ExtArrayIter<'_, T> {
        ExtArrayIter {
            array: self,
            index: 0,
        }
    }

    /// Clears the extensible array, removing and dropping all values and
    /// deallocating all previously allocated segments.
    ///
    /// # Time complexity
    ///
    /// O(n) if elements are droppable, otherwise O(sqrt(n))
    pub fn clear(&mut self) {
        use std::ptr::{drop_in_place, slice_from_raw_parts_mut};

        if self.count > 0 {
            if std::mem::needs_drop::<T>() {
                // find the last segment that contains values and drop them
                let (last_segment, last_slot) = mapping(self.count - 1);
                unsafe {
                    // last_slot is pointing at the last element, need to add
                    // one to include it in the slice
                    drop_in_place(slice_from_raw_parts_mut(
                        self.dope[last_segment],
                        last_slot + 1,
                    ));
                }

                // drop the values in all of the preceding segments
                let mut segment = 0;
                for level in 1..=self.level {
                    let level_limit = last_segment_for_l(level);
                    let segment_len = segment_len_for_l(level);
                    while segment <= level_limit && segment < last_segment {
                        unsafe {
                            drop_in_place(slice_from_raw_parts_mut(
                                self.dope[segment],
                                segment_len,
                            ));
                        }
                        segment += 1;
                    }
                }
            }

            self.level = 1;
            self.count = 0;
        }

        // deallocate all of the segments
        for segment in 0..self.dope.len() {
            let segment_len = slots_in_segment(segment);
            let layout = Layout::array::<T>(segment_len).expect("unexpected overflow");
            unsafe {
                dealloc(self.dope[segment] as *mut u8, layout);
            }
        }
        self.dope.clear();
    }
}

impl<T> Default for ExtensibleArray<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> fmt::Display for ExtensibleArray<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let longest_segment = segment_len_for_l(self.level);
        write!(
            f,
            "ExtensibleArray(count: {}, level: {}, used_segments: {}, longest segment: {})",
            self.count,
            self.level,
            self.dope.len(),
            longest_segment
        )
    }
}

impl<T> Drop for ExtensibleArray<T> {
    fn drop(&mut self) {
        self.clear();
    }
}

impl<T> Index<usize> for ExtensibleArray<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        let Some(item) = self.get(index) else {
            panic!("index out of bounds: {}", index);
        };
        item
    }
}

impl<T> IndexMut<usize> for ExtensibleArray<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let Some(item) = self.get_mut(index) else {
            panic!("index out of bounds: {}", index);
        };
        item
    }
}

impl<A> FromIterator<A> for ExtensibleArray<A> {
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        let mut arr: ExtensibleArray<A> = ExtensibleArray::new();
        for value in iter {
            arr.push(value)
        }
        arr
    }
}

/// Immutable extensible array iterator.
pub struct ExtArrayIter<'a, T> {
    array: &'a ExtensibleArray<T>,
    index: usize,
}

impl<'a, T> Iterator for ExtArrayIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let value = self.array.get(self.index);
        self.index += 1;
        value
    }
}

/// An iterator that moves out of a extensible array.
pub struct ExtArrayIntoIter<T> {
    index: usize,
    count: usize,
    level: usize,
    dope: Vec<*mut T>,
}

impl<T> Iterator for ExtArrayIntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.count {
            let (segment, slot) = mapping(self.index);
            self.index += 1;
            unsafe { Some((self.dope[segment].add(slot)).read()) }
        } else {
            None
        }
    }
}

impl<T> Drop for ExtArrayIntoIter<T> {
    fn drop(&mut self) {
        use std::ptr::{drop_in_place, slice_from_raw_parts_mut};

        if std::mem::needs_drop::<T>() {
            let (first_segment, first_slot) = mapping(self.index);
            let (last_segment, last_slot) = mapping(self.count - 1);
            if first_segment == last_segment {
                // special-case, remaining values are in only one segment
                if first_slot <= last_slot {
                    unsafe {
                        // last_slot is pointing at the last element, need to
                        // add one to include it in the slice
                        drop_in_place(slice_from_raw_parts_mut(
                            self.dope[first_segment].add(first_slot),
                            last_slot - first_slot + 1,
                        ));
                    }
                }
            } else {
                // drop the remaining values in the first segment
                let segment_len = slots_in_segment(first_segment);
                if segment_len < self.count {
                    unsafe {
                        drop_in_place(slice_from_raw_parts_mut(
                            self.dope[first_segment].add(first_slot),
                            segment_len - first_slot,
                        ));
                    }
                }

                // drop the values in the last segment
                unsafe {
                    drop_in_place(slice_from_raw_parts_mut(
                        self.dope[last_segment],
                        last_slot + 1,
                    ));
                }

                // drop the values in all of the other segments
                for segment in first_segment + 1..last_segment {
                    let segment_len = slots_in_segment(segment);
                    unsafe {
                        drop_in_place(slice_from_raw_parts_mut(self.dope[segment], segment_len));
                    }
                }
            }
        }

        // deallocate all of the segments
        for segment in 0..self.dope.len() {
            let segment_len = slots_in_segment(segment);
            let layout = Layout::array::<T>(segment_len).expect("unexpected overflow");
            unsafe {
                dealloc(self.dope[segment] as *mut u8, layout);
            }
        }

        self.dope.clear();
        self.index = 0;
        self.level = 1;
        self.count = 0;
    }
}

impl<T> IntoIterator for ExtensibleArray<T> {
    type Item = T;
    type IntoIter = ExtArrayIntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        let mut me = std::mem::ManuallyDrop::new(self);
        let dope = std::mem::take(&mut me.dope);
        ExtArrayIntoIter {
            index: 0,
            count: me.count,
            level: me.level,
            dope,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_push_get_one_item() {
        let item = String::from("hello world");
        let mut sut: ExtensibleArray<String> = ExtensibleArray::new();
        assert_eq!(sut.len(), 0);
        assert!(sut.is_empty());
        sut.push(item);
        assert_eq!(sut.len(), 1);
        assert!(!sut.is_empty());
        let maybe = sut.get(0);
        assert!(maybe.is_some());
        let actual = maybe.unwrap();
        assert_eq!("hello world", actual);
        let missing = sut.get(10);
        assert!(missing.is_none());
    }

    #[test]
    fn test_push_get_several_strings() {
        let inputs = [
            "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
        ];
        let mut sut: ExtensibleArray<String> = ExtensibleArray::new();
        for item in inputs {
            sut.push(item.to_owned());
        }
        assert_eq!(sut.len(), 9);
        for (idx, item) in inputs.iter().enumerate() {
            let maybe = sut.get(idx);
            assert!(maybe.is_some(), "{idx} is none");
            let actual = maybe.unwrap();
            assert_eq!(item, actual);
        }
        let maybe = sut.get(10);
        assert!(maybe.is_none());
        assert_eq!(sut[3], "four");
    }

    #[test]
    fn test_push_get_hundred_ints() {
        let mut sut: ExtensibleArray<i32> = ExtensibleArray::new();
        for value in 0..100 {
            sut.push(value);
        }
        assert_eq!(sut.len(), 100);
        for idx in 0..100 {
            let maybe = sut.get(idx);
            assert!(maybe.is_some(), "{idx} is none");
            let actual = maybe.unwrap();
            assert_eq!(idx, *actual as usize);
        }
        assert_eq!(sut[99], 99);
    }

    #[test]
    fn test_len_and_capacity() {
        let mut sut: ExtensibleArray<i32> = ExtensibleArray::new();
        assert_eq!(sut.len(), 0);
        assert_eq!(sut.capacity(), 0);
        for value in 0..100 {
            sut.push(value);
        }
        assert_eq!(sut.len(), 100);
        // 2 * 2 + 4 * 3 + 8 * 6 + 16 * 3
        assert_eq!(sut.capacity(), 112);
    }

    #[test]
    fn test_push_within_capacity() {
        // empty array has no allocated space
        let mut sut: ExtensibleArray<u32> = ExtensibleArray::new();
        assert_eq!(sut.push_within_capacity(101), Err(101));
        sut.push(10);
        assert_eq!(sut.push_within_capacity(101), Ok(()));

        // edge case (first segment is 2 elements long)
        let mut sut: ExtensibleArray<u32> = ExtensibleArray::new();
        sut.push(1);
        assert_eq!(sut.push_within_capacity(2), Ok(()));
        assert_eq!(sut.push_within_capacity(3), Err(3));
    }

    #[test]
    fn test_get_mut_index_mut() {
        let mut sut: ExtensibleArray<String> = ExtensibleArray::new();
        sut.push(String::from("first"));
        sut.push(String::from("second"));
        sut.push(String::from("third"));
        if let Some(value) = sut.get_mut(1) {
            value.push_str(" place");
        } else {
            panic!("get_mut() returned None")
        }
        assert_eq!(sut[1], "second place");
        sut[2] = "third planet".into();
        assert_eq!(sut[2], "third planet");
    }

    #[test]
    #[should_panic(expected = "index out of bounds:")]
    fn test_index_out_of_bounds() {
        let mut sut: ExtensibleArray<i32> = ExtensibleArray::new();
        sut.push(10);
        sut.push(20);
        let _ = sut[2];
    }

    #[test]
    #[should_panic(expected = "index out of bounds:")]
    fn test_index_mut_out_of_bounds() {
        let mut sut: ExtensibleArray<i32> = ExtensibleArray::new();
        sut.push(10);
        sut.push(20);
        sut[2] = 30;
    }

    #[test]
    fn test_push_many_pop_all_verify() {
        // push many values, then pop all off and verify
        let mut sut: ExtensibleArray<usize> = ExtensibleArray::new();
        for value in 0..16384 {
            sut.push(value);
        }
        for value in (0..16384).rev() {
            assert_eq!(sut.pop(), Some(value));
        }
    }

    #[test]
    fn test_push_pop_iter() {
        let inputs = [
            "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
        ];
        let mut sut: ExtensibleArray<String> = ExtensibleArray::new();
        assert!(sut.pop().is_none());
        for item in inputs {
            sut.push(item.to_owned());
        }
        assert_eq!(sut.len(), 9);
        for (idx, elem) in sut.iter().enumerate() {
            assert_eq!(inputs[idx], elem);
        }
        let maybe = sut.pop();
        assert!(maybe.is_some());
        let value = maybe.unwrap();
        assert_eq!(value, "nine");
        assert_eq!(sut.len(), 8);
        sut.push(String::from("nine"));
        assert_eq!(sut.len(), 9);
        for (idx, elem) in sut.iter().enumerate() {
            assert_eq!(inputs[idx], elem);
        }

        // pop everything and add back again
        while !sut.is_empty() {
            sut.pop();
        }
        assert_eq!(sut.len(), 0);
        for item in inputs {
            sut.push(item.to_owned());
        }
        assert_eq!(sut.len(), 9);
        for (idx, elem) in sut.iter().enumerate() {
            assert_eq!(inputs[idx], elem);
        }
    }

    #[test]
    fn test_pop_if() {
        let mut sut: ExtensibleArray<u32> = ExtensibleArray::new();
        assert!(sut.pop_if(|_| panic!("should not be called")).is_none());
        for value in 0..10 {
            sut.push(value);
        }
        assert!(sut.pop_if(|_| false).is_none());
        let maybe = sut.pop_if(|v| *v == 9);
        assert_eq!(maybe.unwrap(), 9);
        assert!(sut.pop_if(|v| *v == 9).is_none());
    }

    #[test]
    fn test_swap_remove_single_segment() {
        let mut sut: ExtensibleArray<u32> = ExtensibleArray::new();
        sut.push(1);
        sut.push(2);
        assert_eq!(sut.len(), 2);
        let one = sut.swap_remove(0);
        assert_eq!(one, 1);
        assert_eq!(sut[0], 2);
    }

    #[test]
    fn test_swap_remove_multiple_segments() {
        let mut sut: ExtensibleArray<u32> = ExtensibleArray::new();
        for value in 0..512 {
            sut.push(value);
        }
        assert_eq!(sut.len(), 512);
        let eighty = sut.swap_remove(80);
        assert_eq!(eighty, 80);
        assert_eq!(sut.pop(), Some(510));
        assert_eq!(sut[80], 511);
    }

    #[test]
    #[should_panic(expected = "swap_remove index (is 0) should be < len (is 0)")]
    fn test_swap_remove_panic_empty() {
        let mut sut: ExtensibleArray<u32> = ExtensibleArray::new();
        sut.swap_remove(0);
    }

    #[test]
    #[should_panic(expected = "swap_remove index (is 1) should be < len (is 1)")]
    fn test_swap_remove_panic_range_edge() {
        let mut sut: ExtensibleArray<u32> = ExtensibleArray::new();
        sut.push(1);
        sut.swap_remove(1);
    }

    #[test]
    #[should_panic(expected = "swap_remove index (is 2) should be < len (is 1)")]
    fn test_swap_remove_panic_range_exceed() {
        let mut sut: ExtensibleArray<u32> = ExtensibleArray::new();
        sut.push(1);
        sut.swap_remove(2);
    }

    #[test]
    fn test_clear_and_reuse_tiny() {
        // clear an array that allocated only one segment
        let mut sut: ExtensibleArray<String> = ExtensibleArray::new();
        sut.push(String::from("one"));
        sut.push(String::from("two"));
        assert_eq!(sut.len(), 2);
        sut.clear();
        assert_eq!(sut.len(), 0);
        sut.push(String::from("one"));
        sut.push(String::from("two"));
        assert_eq!(sut.len(), 2);
        // implicitly drop()
    }

    #[test]
    fn test_clear_and_reuse_ints() {
        let mut sut: ExtensibleArray<i32> = ExtensibleArray::new();
        for value in 0..512 {
            sut.push(value);
        }
        assert_eq!(sut.len(), 512);
        sut.clear();
        assert_eq!(sut.len(), 0);
        for value in 0..512 {
            sut.push(value);
        }
        for idx in 0..512 {
            let maybe = sut.get(idx);
            assert!(maybe.is_some(), "{idx} is none");
            let actual = maybe.unwrap();
            assert_eq!(idx, *actual as usize);
        }
    }

    #[test]
    fn test_clear_and_reuse_strings() {
        let mut sut: ExtensibleArray<String> = ExtensibleArray::new();
        for _ in 0..512 {
            let value = ulid::Ulid::new().to_string();
            sut.push(value);
        }
        assert_eq!(sut.len(), 512);
        sut.clear();
        assert_eq!(sut.len(), 0);
        for _ in 0..512 {
            let value = ulid::Ulid::new().to_string();
            sut.push(value);
        }
        assert_eq!(sut.len(), 512);
        // implicitly drop()
    }

    #[test]
    fn test_push_get_thousands_structs() {
        struct MyData {
            a: u64,
            b: i32,
        }
        let mut sut: ExtensibleArray<MyData> = ExtensibleArray::new();
        for value in 0..88_888i32 {
            sut.push(MyData {
                a: value as u64,
                b: value,
            });
        }
        assert_eq!(sut.len(), 88_888);
        for idx in 0..88_888i32 {
            let maybe = sut.get(idx as usize);
            assert!(maybe.is_some(), "{idx} is none");
            let actual = maybe.unwrap();
            assert_eq!(idx as u64, actual.a);
            assert_eq!(idx, actual.b);
        }
    }

    #[test]
    fn test_array_fromiterator() {
        let mut inputs: Vec<i32> = Vec::new();
        for value in 0..10_000 {
            inputs.push(value);
        }
        let sut: ExtensibleArray<i32> = inputs.into_iter().collect();
        assert_eq!(sut.len(), 10_000);
        for idx in 0..10_000i32 {
            let maybe = sut.get(idx as usize);
            assert!(maybe.is_some(), "{idx} is none");
            let actual = maybe.unwrap();
            assert_eq!(idx, *actual);
        }
    }

    #[test]
    fn test_push_get_many_ints() {
        let mut sut: ExtensibleArray<i32> = ExtensibleArray::new();
        for value in 0..1_000_000 {
            sut.push(value);
        }
        assert_eq!(sut.len(), 1_000_000);
        for idx in 0..1_000_000 {
            let maybe = sut.get(idx);
            assert!(maybe.is_some(), "{idx} is none");
            let actual = maybe.unwrap();
            assert_eq!(idx, *actual as usize);
        }
        assert_eq!(sut[99_999], 99_999);
    }

    #[test]
    fn test_array_iterator() {
        let inputs = [
            "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
        ];
        let mut sut: ExtensibleArray<String> = ExtensibleArray::new();
        for item in inputs {
            sut.push(item.to_owned());
        }
        for (idx, elem) in sut.iter().enumerate() {
            assert_eq!(inputs[idx], elem);
        }
    }

    #[test]
    fn test_array_intoiterator() {
        // an array that only requires a single segment
        let inputs = [
            "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
        ];
        let mut sut: ExtensibleArray<String> = ExtensibleArray::new();
        for item in inputs {
            sut.push(item.to_owned());
        }
        for (idx, elem) in sut.into_iter().enumerate() {
            assert_eq!(inputs[idx], elem);
        }
        // sut.len(); // error: ownership of sut was moved
    }

    #[test]
    fn test_array_intoiterator_drop_tiny() {
        // an array that only requires a single segment and only some need to be
        // dropped after partially iterating the values
        let inputs = [
            "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
        ];
        let mut sut: ExtensibleArray<String> = ExtensibleArray::new();
        for item in inputs {
            sut.push(item.to_owned());
        }
        for (idx, _) in sut.into_iter().enumerate() {
            if idx > 2 {
                break;
            }
        }
        // implicitly drop()
    }

    #[test]
    fn test_array_intoiterator_drop_large() {
        // by adding 512 values and iterating less than 64 times, there will be
        // values in the first segment and some in the last segment, and two
        // segments inbetween that all need to be dropped
        let mut sut: ExtensibleArray<String> = ExtensibleArray::new();
        for _ in 0..512 {
            let value = ulid::Ulid::new().to_string();
            sut.push(value);
        }
        for (idx, _) in sut.into_iter().enumerate() {
            if idx >= 30 {
                break;
            }
        }
        // implicitly drop()
    }

    #[test]
    fn test_push_get_many_instances_ints() {
        // test allocating, filling, and then dropping many instances
        for _ in 0..1_000 {
            let mut sut: ExtensibleArray<usize> = ExtensibleArray::new();
            for value in 0..10_000 {
                sut.push(value);
            }
            assert_eq!(sut.len(), 10_000);
        }
    }

    #[test]
    fn test_push_get_many_instances_strings() {
        // test allocating, filling, and then dropping many instances
        for _ in 0..1_000 {
            let mut sut: ExtensibleArray<String> = ExtensibleArray::new();
            for _ in 0..1_000 {
                let value = ulid::Ulid::new().to_string();
                sut.push(value);
            }
            assert_eq!(sut.len(), 1_000);
        }
    }

    #[test]
    fn test_last_segment() {
        // l cannot be zero, but segment numbers are 0-based
        assert_eq!(last_segment_for_l(1), 1);
        assert_eq!(last_segment_for_l(2), 4);
        assert_eq!(last_segment_for_l(3), 10);
        assert_eq!(last_segment_for_l(4), 22);
        assert_eq!(last_segment_for_l(5), 46);
        assert_eq!(last_segment_for_l(6), 94);
        assert_eq!(last_segment_for_l(7), 190);
        assert_eq!(last_segment_for_l(8), 382);
        assert_eq!(last_segment_for_l(9), 766);
        assert_eq!(last_segment_for_l(10), 1534);
        assert_eq!(last_segment_for_l(11), 3070);
        assert_eq!(last_segment_for_l(12), 6142);
        assert_eq!(last_segment_for_l(13), 12286);
        assert_eq!(last_segment_for_l(14), 24574);
        assert_eq!(last_segment_for_l(15), 49150);
        assert_eq!(last_segment_for_l(16), 98302);
    }

    #[test]
    fn test_segment_len() {
        // l cannot be zero, but segment numbers are 0-based
        assert_eq!(segment_len_for_l(1), 2);
        assert_eq!(segment_len_for_l(2), 4);
        assert_eq!(segment_len_for_l(3), 8);
        assert_eq!(segment_len_for_l(4), 16);
        assert_eq!(segment_len_for_l(5), 32);
        assert_eq!(segment_len_for_l(6), 64);
        assert_eq!(segment_len_for_l(7), 128);
        assert_eq!(segment_len_for_l(8), 256);
        assert_eq!(segment_len_for_l(9), 512);
        assert_eq!(segment_len_for_l(10), 1024);
        assert_eq!(segment_len_for_l(11), 2048);
        assert_eq!(segment_len_for_l(12), 4096);
        assert_eq!(segment_len_for_l(13), 8192);
        assert_eq!(segment_len_for_l(14), 16384);
        assert_eq!(segment_len_for_l(15), 32768);
        assert_eq!(segment_len_for_l(16), 65536);
    }

    #[test]
    fn test_mapping() {
        assert_eq!(mapping(0), (0, 0));
        assert_eq!(mapping(1), (0, 1));
        assert_eq!(mapping(2), (1, 0));
        assert_eq!(mapping(3), (1, 1));
        assert_eq!(mapping(4), (2, 0));
        assert_eq!(mapping(72), (11, 8));
        assert_eq!(mapping(248), (22, 8));
        assert_eq!(mapping(4567), (98, 87)); // from the Moffat 2022 paper
        assert_eq!(mapping(1_048_576), (1535, 0));
        assert_eq!(mapping(2_000_000), (1999, 1152));
        assert_eq!(mapping(4_194_304), (3071, 0));
        assert_eq!(mapping(16_777_216), (6143, 0));
        assert_eq!(mapping(67_108_864), (12287, 0));
        assert_eq!(mapping(268_435_456), (24575, 0));
        assert_eq!(mapping(1_073_741_824), (49151, 0));
        assert_eq!(mapping(2_000_000_000), (63284, 37888));
        assert_eq!(mapping(2_147_483_647), (65534, 65535));
        assert_eq!(mapping(2_147_483_648), (65535, 0));
        assert_eq!(mapping(4_294_967_295), (98302, 65535));
    }

    #[test]
    fn test_capacity_for_count() {
        assert_eq!(capacity_for_count(0, 1), 0);
        assert_eq!(capacity_for_count(2, 1), 2);
        assert_eq!(capacity_for_count(3, 1), 4);
        assert_eq!(capacity_for_count(5, 2), 8);
        assert_eq!(capacity_for_count(10, 2), 12);
        assert_eq!(capacity_for_count(100, 4), 112);
        assert_eq!(capacity_for_count(250, 4), 256);
        assert_eq!(capacity_for_count(310, 5), 320);
        assert_eq!(capacity_for_count(1000, 5), 1024);
        assert_eq!(capacity_for_count(15000, 7), 15104);
    }

    #[test]
    fn test_slots_in_segment() {
        assert_eq!(slots_in_segment(0), 2);
        assert_eq!(slots_in_segment(1), 2);
        assert_eq!(slots_in_segment(2), 4);
        assert_eq!(slots_in_segment(3), 4);
        assert_eq!(slots_in_segment(4), 4);
        assert_eq!(slots_in_segment(5), 8);
        assert_eq!(slots_in_segment(6), 8);
        assert_eq!(slots_in_segment(7), 8);
        assert_eq!(slots_in_segment(8), 8);
        assert_eq!(slots_in_segment(9), 8);
        assert_eq!(slots_in_segment(10), 8);
        assert_eq!(slots_in_segment(11), 16);
        assert_eq!(slots_in_segment(30), 32);
        assert_eq!(slots_in_segment(80), 64);
        assert_eq!(slots_in_segment(170), 128);
        assert_eq!(slots_in_segment(350), 256);
        assert_eq!(slots_in_segment(707), 512);
        assert_eq!(slots_in_segment(1400), 1024);
        assert_eq!(slots_in_segment(3000), 2048);
        assert_eq!(slots_in_segment(6000), 4096);
        assert_eq!(slots_in_segment(12000), 8192);
        assert_eq!(slots_in_segment(24000), 16384);
        assert_eq!(slots_in_segment(49000), 32768);
        assert_eq!(slots_in_segment(98000), 65536);
    }

    #[test]
    #[should_panic(expected = "overflow, segment out of bounds")]
    fn test_slots_in_segment_bounds() {
        slots_in_segment(100_000);
    }

    #[test]
    fn test_theory_capacity_for_l() {
        // for the sake of theoretical research...
        //
        // Compute the total volume V(l) of all segments of length less than or
        // equal to 2^l which is simplified to 2^(2*l)
        //
        // N.B. this does not account for the actual allocated segments, so the
        //      value is off by a bit since it only considers the l value
        fn capacity_for_l(l: usize) -> usize {
            1 << (l << 1)
        }

        assert_eq!(capacity_for_l(1), 4);
        assert_eq!(capacity_for_l(2), 16);
        assert_eq!(capacity_for_l(3), 64);
        assert_eq!(capacity_for_l(4), 256);
        assert_eq!(capacity_for_l(5), 1024);
        assert_eq!(capacity_for_l(6), 4096);
        assert_eq!(capacity_for_l(7), 16384);
        assert_eq!(capacity_for_l(8), 65536);
        assert_eq!(capacity_for_l(9), 262_144);
        assert_eq!(capacity_for_l(10), 1_048_576);
        assert_eq!(capacity_for_l(11), 4_194_304);
        assert_eq!(capacity_for_l(12), 16_777_216);
        assert_eq!(capacity_for_l(13), 67_108_864);
        assert_eq!(capacity_for_l(14), 268_435_456);
        assert_eq!(capacity_for_l(15), 1_073_741_824);
        assert_eq!(capacity_for_l(16), 4_294_967_296);
    }

    #[test]
    fn test_theory_num_segments_for_l() {
        // for the sake of theoretical research...
        //
        // Compute the number of segments of the same length for some l.
        fn num_segments_for_l(l: usize) -> usize {
            if l == 1 { 2 } else { 3 * (1 << (l - 2)) }
        }

        // l cannot be zero, but segment numbers are 0-based
        assert_eq!(num_segments_for_l(1), 2);
        assert_eq!(num_segments_for_l(2), 3);
        assert_eq!(num_segments_for_l(3), 6);
        assert_eq!(num_segments_for_l(4), 12);
        assert_eq!(num_segments_for_l(5), 24);
        assert_eq!(num_segments_for_l(6), 48);
        assert_eq!(num_segments_for_l(7), 96);
        assert_eq!(num_segments_for_l(8), 192);
        assert_eq!(num_segments_for_l(9), 384);
        assert_eq!(num_segments_for_l(10), 768);
        assert_eq!(num_segments_for_l(11), 1536);
        assert_eq!(num_segments_for_l(12), 3072);
        assert_eq!(num_segments_for_l(13), 6144);
        assert_eq!(num_segments_for_l(14), 12288);
        assert_eq!(num_segments_for_l(15), 24576);
        assert_eq!(num_segments_for_l(16), 49152);
    }
}
