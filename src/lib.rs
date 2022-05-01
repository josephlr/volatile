//! Provides the wrapper type `Volatile`, which wraps a reference to any copy-able type and allows
//! for volatile memory access to wrapped value. Volatile memory accesses are never optimized away
//! by the compiler, and are useful in many low-level systems programming and concurrent contexts.
//!
//! The wrapper types *do not* enforce any atomicity guarantees; to also get atomicity, consider
//! looking at the `Atomic` wrapper types found in `libcore` or `libstd`.

#![no_std]
#![cfg_attr(
    feature = "const_fn",
    feature(
        const_maybe_uninit_as_mut_ptr,
        const_mut_refs,
        const_trait_impl,
        const_slice_ptr_len,
        slice_ptr_len,
        slice_ptr_get,
        nonnull_slice_from_raw_parts,
        const_slice_index,
    )
)]
#![allow(missing_docs)]
#![deny(unsafe_op_in_unsafe_fn)]

use core::{
    fmt,
    marker::PhantomData,
    mem::MaybeUninit,
    ptr::{self, NonNull},
};

pub mod access;
use access::*;
#[cfg(test)]
mod tests;
pub mod traits;

pub type ReadWrite = (SafeAccess, SafeAccess);
pub type ReadOnly = (SafeAccess, NoAccess);
pub type WriteOnly = (NoAccess, SafeAccess);

/// Wraps a reference or pointer to make accesses to the referenced value volatile.
///
/// Similar to a reference, this struct contains a lifetime indicating for how
/// long accesses to the underlying `T` should be allowed. The size and layout
/// of this struct are the same as a [`NonNull<T>`]. `T` needs to be [`Copy`]
/// for TODO(add method link), as volatile operations take and return copies of the value.
///
/// Since not all volatile resources (e.g. memory mapped device registers) are
/// both readable and writable, this type supports limiting the allowed access
/// types through an optional second generic parameter `A`. This should ve an
/// [`Access`] type such as:
///   - [`ReadWrite`]: the default, allows reads and writes
///   - [`ReadOnly`]: only allows reads
///   - [`WriteOnly`]: only allows writes
#[repr(transparent)]
pub struct VolatilePtr<'a, T: ?Sized, A = ReadWrite> {
    ptr: NonNull<T>,
    reference: PhantomData<&'a mut T>,
    access: PhantomData<A>,
}

impl<T: ?Sized, A> Clone for VolatilePtr<'_, T, A> {
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr,
            reference: PhantomData,
            access: PhantomData,
        }
    }
}
impl<T: ?Sized, A> Copy for VolatilePtr<'_, T, A> {}
impl<T: ?Sized, A> fmt::Debug for VolatilePtr<'_, T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("VolatilePtr").field(&self.ptr).finish()
    }
}

impl<'a, T: ?Sized> VolatilePtr<'a, T> {
    /// Constructs a new volatile instance wrapping the given pointer.
    ///
    /// TODO Document safety
    ///
    /// ## Example
    ///
    /// ```rust
    /// # extern crate core;
    /// use volatile::VolatilePtr;
    /// use core::ptr::NonNull;
    ///
    /// let mut value = 0u32;
    ///
    /// let mut volatile = unsafe { VolatilePtr::new(NonNull::from(&mut value)) };
    /// volatile.write(1);
    /// assert_eq!(volatile.read(), 1);
    /// ```
    #[inline]
    pub const unsafe fn new(ptr: NonNull<T>) -> Self {
        unsafe { Self::from_ptr(ptr) }
    }

    #[inline]
    #[cfg_attr(feature = "const_fn", rustversion::attr(all(), const))]
    pub fn from_mut_ref(r: &'a mut T) -> Self {
        let ptr = r as *mut T;
        // SAFETY:
        unsafe { Self::from_ptr(NonNull::new_unchecked(ptr)) }
    }
}

impl<'a, T: ?Sized> VolatilePtr<'a, T, ReadOnly> {
    #[inline]
    pub const unsafe fn new_read_only(ptr: NonNull<T>) -> Self {
        unsafe { Self::from_ptr(ptr) }
    }

    #[inline]
    pub const fn from_ref(r: &'a T) -> Self {
        // TODO: Here and below use const_convert, when it's stable.
        let ptr = r as *const T as *mut T;
        // SAFETY:
        unsafe { Self::from_ptr(NonNull::new_unchecked(ptr)) }
    }
}

impl<'a, T> VolatilePtr<'a, T, WriteOnly> {
    #[inline]
    pub const unsafe fn new_write_only(ptr: NonNull<T>) -> Self {
        unsafe { Self::from_ptr(ptr) }
    }

    #[inline]
    #[cfg_attr(feature = "const_fn", rustversion::attr(all(), const))]
    pub fn from_uninit(u: &'a mut MaybeUninit<T>) -> Self {
        let ptr = u.as_mut_ptr();
        // SAFETY:
        unsafe { Self::from_ptr(NonNull::new_unchecked(ptr)) }
    }
}

impl<'a, T: ?Sized, A> VolatilePtr<'a, T, A> {
    #[inline]
    pub const unsafe fn from_ptr(ptr: NonNull<T>) -> Self {
        Self {
            ptr,
            reference: PhantomData,
            access: PhantomData,
        }
    }

    pub const unsafe fn cast<U>(self) -> VolatilePtr<'a, U, A> {
        unsafe { VolatilePtr::from_ptr(self.ptr.cast()) }
    }

    /// Extracts the inner value stored in the wrapper type.
    ///
    /// This method gives direct access to the wrapped reference and thus allows
    /// non-volatile access again. This is seldom what you want since there is usually
    /// a reason that a reference is wrapped in `Volatile`. However, in some cases it might
    /// be required or useful to use the `read_volatile`/`write_volatile` pointer methods of
    /// the standard library directly, which this method makes possible.
    ///
    /// Since no memory safety violation can occur when accessing the referenced value using
    /// non-volatile operations, this method is safe. However, it _can_ lead to bugs at the
    /// application level, so this method should be used with care.
    ///
    /// ## Example
    ///
    /// ```
    /// # extern crate core;
    /// use volatile::VolatilePtr;
    /// use core::ptr::NonNull;
    ///
    /// let mut value = 42;
    /// let mut volatile = unsafe { VolatilePtr::new_read_write(NonNull::from(&mut value)) };
    /// volatile.write(50);
    /// let unwrapped: *mut i32 = volatile.as_ptr().as_ptr();
    ///
    /// assert_eq!(unsafe { *unwrapped }, 50); // non volatile access, be careful!
    /// ```
    pub fn as_ptr(self) -> NonNull<T> {
        self.ptr
    }

    pub const fn with_access<B: Access>(self) -> VolatilePtr<'a, T, B>
    where
        A: Access,
        A::Read: Allows<B::Read>,
        A::Write: Allows<B::Write>,
    {
        unsafe { VolatilePtr::from_ptr(self.ptr) }
    }
}

// /// TODO
// ///
// /// ## Examples
// ///
// /// Accessing a struct field:
// ///
// /// ```
// /// # extern crate core;
// /// use volatile::{VolatilePtr, map_field};
// /// use core::ptr::NonNull;
// ///
// /// struct Example { field_1: u32, field_2: u8, }
// /// let mut value = Example { field_1: 15, field_2: 255 };
// /// let mut volatile = unsafe { VolatilePtr::new_read_write(NonNull::from(&mut value)) };
// ///
// /// // construct a volatile reference to a field
// /// let field_2 = field!(volatile.field_2);
// /// assert_eq!(field_2.read(), 255);
// /// ```
// #[macro_export]
// macro_rules! field {
//     ($volatile:ident.$place:ident) => {
//         unsafe {
//             $volatile.map(|ptr| {
//                 core::ptr::NonNull::new(core::ptr::addr_of_mut!((*ptr.as_ptr()).$place)).unwrap()
//             })
//         }
//     };
// }

/// Methods for references to `Copy` types
impl<T: Copy, A: Access> VolatilePtr<'_, T, A> {
    /// Performs a volatile read of the contained value.
    ///
    /// Returns a copy of the read value. Volatile reads are guaranteed not to be optimized
    /// away by the compiler, but by themselves do not have atomic ordering
    /// guarantees. To also get atomicity, consider looking at the `Atomic` wrapper types of
    /// the standard/`core` library.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # extern crate core;
    /// use volatile::VolatilePtr;
    /// use core::ptr::NonNull;
    ///
    /// let value = 42;
    /// let shared_reference = unsafe { VolatilePtr::new_read_only(NonNull::from(&value)) };
    /// assert_eq!(shared_reference.read(), 42);
    ///
    /// let mut value = 50;
    /// let mut_reference = unsafe { VolatilePtr::new(NonNull::from(&mut value)) };
    /// assert_eq!(mut_reference.read(), 50);
    /// ```
    pub fn read(self) -> T
    where
        A::Read: Allows<SafeAccess>,
    {
        // UNSAFE: Safe, as ... TODO
        unsafe { self.read_unsafe() }
    }

    /// Performs a volatile write, setting the contained value to the given `value`.
    ///
    /// Volatile writes are guaranteed to not be optimized away by the compiler, but by
    /// themselves do not have atomic ordering guarantees. To also get atomicity, consider
    /// looking at the `Atomic` wrapper types of the standard/`core` library.
    ///
    /// ## Example
    ///
    /// ```rust
    /// # extern crate core;
    /// use volatile::VolatilePtr;
    /// use core::ptr::NonNull;
    ///
    /// let mut value = 42;
    /// let mut volatile = unsafe { VolatilePtr::new(NonNull::from(&mut value)) };
    /// volatile.write(50);
    ///
    /// assert_eq!(volatile.read(), 50);
    /// ```
    pub fn write(self, value: T)
    where
        A::Write: Allows<SafeAccess>,
    {
        // UNSAFE: Safe, as ... TODO
        unsafe { self.write_unsafe(value) };
    }

    /// Updates the contained value using the given closure and volatile instructions.
    ///
    /// Performs a volatile read of the contained value, passes a mutable reference to it to the
    /// function `f`, and then performs a volatile write of the (potentially updated) value back to
    /// the contained value.
    ///
    /// ```rust
    /// # extern crate core;
    /// use volatile::VolatilePtr;
    /// use core::ptr::NonNull;
    ///
    /// let mut value = 42;
    /// let mut volatile = unsafe { VolatilePtr::new(NonNull::from(&mut value)) };
    /// volatile.update(|val| *val += 1);
    ///
    /// assert_eq!(volatile.read(), 43);
    /// ```
    pub fn update<F>(self, f: F)
    where
        A::Read: Allows<SafeAccess>,
        A::Write: Allows<SafeAccess>,
        F: FnOnce(&mut T),
    {
        unsafe { self.update_unsafe(f) }
    }

    pub unsafe fn read_unsafe(self) -> T
    where
        A::Read: Allows<UnsafeAccess>,
    {
        unsafe { ptr::read_volatile(self.ptr.as_ptr()) }
    }

    pub unsafe fn write_unsafe(self, value: T)
    where
        A::Write: Allows<UnsafeAccess>,
    {
        unsafe { ptr::write_volatile(self.ptr.as_ptr(), value) };
    }

    pub unsafe fn update_unsafe<F>(self, f: F)
    where
        A::Read: Allows<UnsafeAccess>,
        A::Write: Allows<UnsafeAccess>,
        F: FnOnce(&mut T),
    {
        let mut value = unsafe { self.read_unsafe() };
        f(&mut value);
        unsafe { self.write_unsafe(value) };
    }
}

/// Transformation methods for accessing struct fields
impl<'a, T: ?Sized, A> VolatilePtr<'a, T, A> {
    /// Constructs a new `Volatile` reference by mapping the wrapped pointer.
    ///
    /// This method is useful for accessing only a part of a volatile value, e.g. a subslice or
    /// a struct field. For struct field access, there is also the safe [`map_field`] macro that
    /// wraps this function.
    ///
    /// ## Examples
    ///
    /// Accessing a struct field:
    ///
    /// ```
    /// # extern crate core;
    /// use volatile::VolatilePtr;
    /// use core::ptr::NonNull;
    ///
    /// struct Example { field_1: u32, field_2: u8, }
    /// let mut value = Example { field_1: 15, field_2: 255 };
    /// let mut volatile = unsafe { VolatilePtr::new_read_write(NonNull::from(&mut value)) };
    ///
    /// // construct a volatile reference to a field
    /// let field_2 = unsafe { volatile.map(|ptr| NonNull::new(core::ptr::addr_of_mut!((*ptr.as_ptr()).field_2)).unwrap()) };
    /// assert_eq!(field_2.read(), 255);
    /// ```
    ///
    /// Don't misuse this method to do a non-volatile read of the referenced value:
    ///
    /// ```
    /// # extern crate core;
    /// use volatile::VolatilePtr;
    /// use core::ptr::NonNull;
    ///
    /// let mut value = 5;
    /// let mut volatile = unsafe { VolatilePtr::new_read_write(NonNull::from(&mut value)) };
    ///
    /// // DON'T DO THIS:
    /// let mut readout = 0;
    /// unsafe { volatile.map(|value| {
    ///    readout = *value.as_ptr(); // non-volatile read, might lead to bugs
    ///    value
    /// })};
    /// ```
    pub const unsafe fn map<F, U: ?Sized>(self, f: F) -> VolatilePtr<'a, U, A>
    where
        F: ~const FnOnce(NonNull<T>) -> NonNull<U>,
    {
        unsafe { VolatilePtr::from_ptr(f(self.ptr)) }
    }
}

/// Methods for transforming volatile slices into other volatile pointers.
impl<'a, T, A> VolatilePtr<'a, [T], A> {
    pub const fn len(&self) -> usize {
        self.ptr.len()
    }

    /// Applies the index operation on the wrapped slice.
    ///
    /// Returns a shared `Volatile` reference to the resulting subslice.
    ///
    /// This is a convenience method for the `map(|slice| slice.index(index))` operation, so it
    /// has the same behavior as the indexing operation on slice (e.g. panic if index is
    /// out-of-bounds).
    ///
    /// ## Examples
    ///
    /// Accessing a single slice element:
    ///
    /// ```
    /// # extern crate core;
    /// use volatile::VolatilePtr;
    /// use core::ptr::NonNull;
    ///
    /// let array = [1, 2, 3];
    /// let slice = &array[..];
    /// let volatile = unsafe { VolatilePtr::new_read_only(NonNull::from(slice)) };
    /// assert_eq!(volatile.index(1).read(), 2);
    /// ```
    ///
    /// Accessing a subslice:
    ///
    /// ```
    /// # extern crate core;
    /// use volatile::VolatilePtr;
    /// use core::ptr::NonNull;
    ///
    /// let array = [1, 2, 3];
    /// let slice = &array[..];
    /// let volatile = unsafe { VolatilePtr::new_read_only(NonNull::from(slice)) };
    /// let subslice = volatile.index(1..);
    /// assert_eq!(subslice.index(0).read(), 2);
    /// ```
    pub const fn index<I>(self, index: I) -> VolatilePtr<'a, I::Output, A>
    where
        I: ~const traits::SliceIndex<[T]>,
    {
        unsafe { VolatilePtr::from_ptr(index.get(self.ptr)) }
    }

    pub const fn split_at(self, mid: usize) -> (VolatilePtr<'a, [T], A>, VolatilePtr<'a, [T], A>) {
        (self.index(..mid), self.index(mid..))
    }

    pub fn as_chunks<const N: usize>(
        self,
    ) -> (VolatilePtr<'a, [[T; N]], A>, VolatilePtr<'a, [T], A>) {
        assert_ne!(N, 0);
        let len = self.ptr.len() / N;
        let (multiple_of_n, remainder) = self.split_at(len * N);
        (multiple_of_n.as_chunks_exact(), remainder)
    }

    pub fn as_chunks_exact<const N: usize>(self) -> VolatilePtr<'a, [[T; N]], A> {
        assert_ne!(N, 0);
        assert_eq!(self.ptr.len() % N, 0);
        let new_len = self.ptr.len() / N;
        // SAFETY: We cast a slice of `new_len * N` elements into
        // a slice of `new_len` many `N` elements chunks.
        let ptr = NonNull::slice_from_raw_parts(self.ptr.cast(), new_len);
        unsafe { VolatilePtr::from_ptr(ptr) }
    }
}

// /// Methods for volatile byte slices
// #[cfg(feature = "unstable")]
// impl<A> VolatilePtr<'_, [u8], A> {
//     /// Sets all elements of the byte slice to the given `value` using a volatile `memset`.
//     ///
//     /// This method is similar to the `slice::fill` method of the standard library, with the
//     /// difference that this method performs a volatile write operation. Another difference
//     /// is that this method is only available for byte slices (not general `&mut [T]` slices)
//     /// because there currently isn't a instrinsic function that allows non-`u8` values.
//     ///
//     /// This method is only available with the `unstable` feature enabled (requires a nightly
//     /// Rust compiler).
//     ///
//     /// ## Example
//     ///
//     /// ```rust
//     /// # extern crate core;
//     /// use volatile::VolatilePtr;
//     /// use core::ptr::NonNull;
//     ///
//     /// let mut buf = unsafe { VolatilePtr::new_read_write(NonNull::from(vec![0; 10].as_mut_slice())) };
//     /// buf.fill(1);
//     /// assert_eq!(unsafe { buf.as_ptr().as_mut() }, &mut vec![1; 10]);
//     /// ```
//     pub fn fill(&mut self, value: u8) {
//         unsafe {
//             intrinsics::volatile_set_memory(self.pointer.as_mut_ptr(), value, self.pointer.len());
//         }
//     }
//     /// Copies all elements from `self` into `dst`, using a volatile memcpy.
//     ///
//     /// The length of `dst` must be the same as `self`.
//     ///
//     /// The method is only available with the `unstable` feature enabled (requires a nightly
//     /// Rust compiler).
//     ///
//     /// ## Panics
//     ///
//     /// This function will panic if the two slices have different lengths.
//     ///
//     /// ## Examples
//     ///
//     /// Copying two elements from a volatile slice:
//     ///
//     /// ```
//     /// # extern crate core;
//     /// use volatile::VolatilePtr;
//     /// use core::ptr::NonNull;
//     ///
//     /// let src = [1, 2];
//     /// // the `Volatile` type does not work with arrays, so convert `src` to a slice
//     /// let slice = &src[..];
//     /// let volatile = unsafe { VolatilePtr::new_read_only(NonNull::from(slice)) };
//     /// let mut dst = [5, 0, 0];
//     ///
//     /// // Because the slices have to be the same length,
//     /// // we slice the destination slice from three elements
//     /// // to two. It will panic if we don't do this.
//     /// volatile.copy_into_slice(&mut dst[1..]);
//     ///
//     /// assert_eq!(src, [1, 2]);
//     /// assert_eq!(dst, [5, 1, 2]);
//     /// ```
//     pub fn copy_into_slice(&self, dst: &mut [T])
//     where
//         T: Copy,
//     {
//         let len = self.pointer.len();
//         assert_eq!(
//             len,
//             dst.len(),
//             "destination and source slices have different lengths"
//         );
//         unsafe {
//             intrinsics::volatile_copy_nonoverlapping_memory(
//                 dst.as_mut_ptr(),
//                 self.pointer.as_mut_ptr(),
//                 len,
//             );
//         }
//     }

//     /// Copies all elements from `src` into `self`, using a volatile memcpy.
//     ///
//     /// The length of `src` must be the same as `self`.
//     ///
//     /// This method is similar to the `slice::copy_from_slice` method of the standard library. The
//     /// difference is that this method performs a volatile copy.
//     ///
//     /// The method is only available with the `unstable` feature enabled (requires a nightly
//     /// Rust compiler).
//     ///
//     /// ## Panics
//     ///
//     /// This function will panic if the two slices have different lengths.
//     ///
//     /// ## Examples
//     ///
//     /// Copying two elements from a slice into a volatile slice:
//     ///
//     /// ```
//     /// # extern crate core;
//     /// use volatile::VolatilePtr;
//     /// use core::ptr::NonNull;
//     ///
//     /// let src = [1, 2, 3, 4];
//     /// let mut dst = [0, 0];
//     /// // the `Volatile` type does not work with arrays, so convert `dst` to a slice
//     /// let slice = &mut dst[..];
//     /// let mut volatile = unsafe { VolatilePtr::new_read_write(NonNull::from(slice))};
//     ///
//     /// // Because the slices have to be the same length,
//     /// // we slice the source slice from four elements
//     /// // to two. It will panic if we don't do this.
//     /// volatile.copy_from_slice(&src[2..]);
//     ///
//     /// assert_eq!(src, [1, 2, 3, 4]);
//     /// assert_eq!(dst, [3, 4]);
//     /// ```
//     pub fn copy_from_slice(&mut self, src: &[T])
//     where
//         T: Copy,
//     {
//         let len = self.pointer.len();
//         assert_eq!(
//             len,
//             src.len(),
//             "destination and source slices have different lengths"
//         );
//         unsafe {
//             intrinsics::volatile_copy_nonoverlapping_memory(
//                 self.pointer.as_mut_ptr(),
//                 src.as_ptr(),
//                 len,
//             );
//         }
//     }

//     /// Copies elements from one part of the slice to another part of itself, using a
//     /// volatile `memmove`.
//     ///
//     /// `src` is the range within `self` to copy from. `dest` is the starting index of the
//     /// range within `self` to copy to, which will have the same length as `src`. The two ranges
//     /// may overlap. The ends of the two ranges must be less than or equal to `self.len()`.
//     ///
//     /// This method is similar to the `slice::copy_within` method of the standard library. The
//     /// difference is that this method performs a volatile copy.
//     ///
//     /// This method is only available with the `unstable` feature enabled (requires a nightly
//     /// Rust compiler).
//     ///
//     /// ## Panics
//     ///
//     /// This function will panic if either range exceeds the end of the slice, or if the end
//     /// of `src` is before the start.
//     ///
//     /// ## Examples
//     ///
//     /// Copying four bytes within a slice:
//     ///
//     /// ```
//     /// extern crate core;
//     /// use volatile::VolatilePtr;
//     /// use core::ptr::NonNull;
//     ///
//     /// let mut byte_array = *b"Hello, World!";
//     /// let mut slice: &mut [u8] = &mut byte_array[..];
//     /// let mut volatile = unsafe { VolatilePtr::new_read_write(NonNull::from(slice)) };
//     ///
//     /// volatile.copy_within(1..5, 8);
//     ///
//     /// assert_eq!(&byte_array, b"Hello, Wello!");
//     pub fn copy_within(&mut self, src: impl RangeBounds<usize>, dest: usize)
//     where
//         T: Copy,
//     {
//         let len = self.pointer.len();
//         // implementation taken from https://github.com/rust-lang/rust/blob/683d1bcd405727fcc9209f64845bd3b9104878b8/library/core/src/slice/mod.rs#L2726-L2738
//         let Range {
//             start: src_start,
//             end: src_end,
//         } = range(src, ..len);
//         let count = src_end - src_start;
//         assert!(dest <= len - count, "dest is out of bounds");
//         // SAFETY: the conditions for `volatile_copy_memory` have all been checked above,
//         // as have those for `ptr::add`.
//         unsafe {
//             intrinsics::volatile_copy_memory(
//                 self.pointer.as_mut_ptr().add(dest),
//                 self.pointer.as_mut_ptr().add(src_start),
//                 count,
//             );
//         }
//     }
// }

// /// Methods for converting arrays to slices
// ///
// /// These methods are only available with the `unstable` feature enabled (requires a nightly
// /// Rust compiler).
// #[cfg(feature = "unstable")]
// impl<T, R, W, const N: usize> VolatilePtr<'_, [T; N], Access<R, W>> {
//     /// Converts an array reference to a shared slice.
//     ///
//     /// This makes it possible to use the methods defined on slices.
//     ///
//     /// ## Example
//     ///
//     /// Copying two elements from a volatile array reference using `copy_into_slice`:
//     ///
//     /// ```
//     /// # extern crate core;
//     /// use volatile::VolatilePtr;
//     /// use core::ptr::NonNull;
//     ///
//     /// let src = [1, 2];
//     /// let volatile = unsafe { VolatilePtr::new_read_only(NonNull::from(&src)) };
//     /// let mut dst = [0, 0];
//     ///
//     /// // convert the `Volatile<&[i32; 2]>` array reference to a `Volatile<&[i32]>` slice
//     /// let volatile_slice = volatile.as_slice();
//     /// // we can now use the slice methods
//     /// volatile_slice.copy_into_slice(&mut dst);
//     ///
//     /// assert_eq!(dst, [1, 2]);
//     /// ```
//     pub fn as_slice(&self) -> VolatilePtr<[T], Access<R, access::NoAccess>> {
//         unsafe {
//             self.map(|array| {
//                 NonNull::new(ptr::slice_from_raw_parts_mut(array.as_ptr() as *mut T, N)).unwrap()
//             })
//         }
//     }
// }

// /// Methods for restricting access.
// impl<'a, T, R, W> VolatilePtr<'a, T, Access<R, W>>
// where
//     T: ?Sized,
// {
//     /// Restricts access permissions to read-only.
//     ///
//     /// ## Example
//     ///
//     /// ```
//     /// # extern crate core;
//     /// use volatile::VolatilePtr;
//     /// use core::ptr::NonNull;
//     ///
//     /// let mut value: i16 = -4;
//     /// let mut volatile = unsafe { VolatilePtr::new_read_write(NonNull::from(&mut value)) };
//     ///
//     /// let read_only = volatile.read_only();
//     /// assert_eq!(read_only.read(), -4);
//     /// // read_only.write(10); // compile-time error
//     /// ```
//     pub fn read_only(self) -> VolatilePtr<'a, T, Access<R, access::NoAccess>> {
//         unsafe { VolatilePtr::new_generic(self.pointer) }
//     }

//     /// Restricts access permissions to write-only.
//     ///
//     /// ## Example
//     ///
//     /// Creating a write-only reference to a struct field:
//     ///
//     /// ```
//     /// # extern crate core;
//     /// use volatile::{VolatilePtr, map_field_mut};
//     /// use core::ptr::NonNull;
//     ///
//     /// struct Example { field_1: u32, field_2: u8, }
//     /// let mut value = Example { field_1: 15, field_2: 255 };
//     /// let mut volatile = unsafe { VolatilePtr::new_read_write(NonNull::from(&mut value)) };
//     ///
//     /// // construct a volatile write-only reference to `field_2`
//     /// let mut field_2 = map_field_mut!(volatile.field_2).write_only();
//     /// field_2.write(14);
//     /// // field_2.read(); // compile-time error
//     /// ```
//     pub fn write_only(self) -> VolatilePtr<'a, T, Access<access::NoAccess, W>> {
//         unsafe { VolatilePtr::new_generic(self.pointer) }
//     }
// }

// impl<T, W> fmt::Debug for VolatilePtr<'_, T, Access<access::SafeAccess, W>>
// where
//     T: Copy + fmt::Debug + ?Sized,
// {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         f.debug_tuple("Volatile").field(&self.read()).finish()
//     }
// }

// impl<T, W> fmt::Debug for VolatilePtr<'_, T, Access<access::UnsafeAccess, W>>
// where
//     T: ?Sized,
// {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         f.debug_tuple("Volatile").field(&"[unsafe read]").finish()
//     }
// }

// impl<T, W> fmt::Debug for VolatilePtr<'_, T, Access<access::NoAccess, W>>
// where
//     T: ?Sized,
// {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         f.debug_tuple("Volatile")
//             .field(&"[no read access]")
//             .finish()
//     }
// }
