use core::{
    ops::{RangeFrom, RangeTo},
    ptr::NonNull,
};

pub unsafe trait SliceIndex<T: ?Sized> {
    type Output: ?Sized;
    unsafe fn get(self, slice: NonNull<T>) -> NonNull<Self::Output>;
}

unsafe impl<T> const SliceIndex<[T]> for RangeTo<usize> {
    type Output = [T];
    unsafe fn get(self, slice: NonNull<[T]>) -> NonNull<Self::Output> {
        // Add bounds checks
        unsafe { slice.get_unchecked_mut(self) }
    }
}

unsafe impl<T> const SliceIndex<[T]> for RangeFrom<usize> {
    type Output = [T];
    unsafe fn get(self, slice: NonNull<[T]>) -> NonNull<Self::Output> {
        // Add bounds checks
        unsafe { slice.get_unchecked_mut(self) }
    }
}
