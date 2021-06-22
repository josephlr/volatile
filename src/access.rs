#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct NoAccess;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct UnsafeAccess;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SafeAccess;

pub trait Unsafe {}
pub trait Safe: Unsafe {}

impl Unsafe for UnsafeAccess {}
impl Unsafe for SafeAccess {}
impl Safe for SafeAccess {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Access<R, W>(R, W);

pub type ReadOnly = Access<SafeAccess, NoAccess>;
pub type WriteOnly = Access<NoAccess, SafeAccess>;
pub type ReadWrite = Access<SafeAccess, SafeAccess>;
