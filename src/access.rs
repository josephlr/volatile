pub struct NoAccess(());
pub struct UnsafeAccess(());
pub struct SafeAccess(());

/// A type implements this trait if all the operations in `A` are also allowed
/// for this type. Phrased otherwise, the permitted operations for `A` are a
/// subset of the permitted operations for `Self`.
pub unsafe trait Allows<A> {}

unsafe impl Allows<SafeAccess> for SafeAccess {}
unsafe impl<T: Allows<SafeAccess>> Allows<UnsafeAccess> for T {}
unsafe impl Allows<UnsafeAccess> for UnsafeAccess {}
unsafe impl<T: Allows<UnsafeAccess>> Allows<NoAccess> for T {}
unsafe impl Allows<NoAccess> for NoAccess {}

/// A trait representing a set of premitted Read and Write operations.
pub trait Access {
    type Read;
    type Write;
}

impl<Read, Write> Access for (Read, Write) {
    type Read = Read;
    type Write = Write;
}
