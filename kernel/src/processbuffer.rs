// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

//! Data structures for passing application memory to the kernel.
//!
//! A Tock process can pass read-write or read-only buffers into the
//! kernel for it to use. The kernel checks that read-write buffers
//! exist within a process's RAM address space, and that read-only
//! buffers exist either within its RAM or flash address space. These
//! buffers are shared with the allow_read_write() and
//! allow_read_only() system calls.
//!
//! A read-write and read-only call is mapped to the high-level Rust
//! types [`ReadWriteProcessBuffer`] and [`ReadOnlyProcessBuffer`]
//! respectively. The memory regions can be accessed through the
//! [`ReadableProcessBuffer`] and [`WriteableProcessBuffer`] traits,
//! implemented on the process buffer structs.
//!
//! Each access to the buffer structs requires a liveness check to ensure that
//! the process memory is still valid. For a more traditional interface, users
//! can convert buffers into [`ReadableProcessSlice`] or
//! [`WriteableProcessSlice`] and use these for the lifetime of their
//! operations. Users cannot hold live-lived references to these slices,
//! however.

use core::cell::Cell;
use core::marker::PhantomData;
use core::ops::{Deref, Index, Range, RangeFrom, RangeTo};

use crate::capabilities;
use crate::process::{self, ProcessId};
use crate::ErrorCode;

/// Get a valid non-null from a range in process memory.
/// # Safety requirements
/// If len is non-zero, ptr must be non zero.
///
pub unsafe fn raw_processbuf_to_nonnul(ptr: *const u8, len: usize) -> NonNull<[u8]> {
    // Rust has very strict requirements on pointer validity[1]
    // which also in part apply to accesses of length 0. We allow
    // an application to supply arbitrary pointers if the buffer
    // length is 0, but this is not allowed for Rust slices. For
    // instance, a null pointer is _never_ valid, not even for
    // accesses of size zero.
    //
    // To get a pointer which does not point to valid (allocated)
    // memory, but is safe to construct for accesses of size zero,
    // we must call NonNull::dangling(). The resulting pointer is
    // guaranteed to be well-aligned and uphold the guarantees
    // required for accesses of size zero.
    //
    // [1]: https://doc.rust-lang.org/core/ptr/index.html#safety
    match len {
        0 => NonNull::slice_from_raw_parts(core::ptr::NonNull::<u8>::dangling(), 0),
        _ => NonNull::slice_from_raw_parts(NonNull::new_unchecked(ptr as *mut u8), len),
    }
}

/// Convert a process buffer's internal representation to a
/// [`ReadableProcessSlice`].
///
/// This function will automatically convert zero-length process
/// buffers into valid zero-sized Rust slices regardless of the value
/// of `ptr`.
///
/// # Safety requirements
///
/// In the case of `len != 0`, the memory `[ptr; ptr + len)` must be
/// within a single process' address space, and `ptr` must be
/// nonzero. This memory region must be mapped as _readable_, and
/// optionally _writable_ and _executable_. It must be allocated
/// within a single process' address space for the entire lifetime
/// `'a`.
///
/// It is sound for multiple overlapping [`ReadableProcessSlice`]s or
/// [`WriteableProcessSlice`]s to be in scope at the same time.
pub unsafe fn raw_processbuf_to_roprocessslice<'a>(
    ptr: *const u8,
    len: usize,
) -> &'a ReadableProcessSlice {
    // Transmute a reference to a slice of Cell<u8>s into a reference
    // to a ReadableProcessSlice. This is possible as
    // ReadableProcessSlice is a #[repr(transparent)] wrapper around a
    // [ReadableProcessByte], which is a #[repr(transparent)] wrapper
    // around a [Cell<u8>], which is a #[repr(transparent)] wrapper
    // around an [UnsafeCell<u8>], which finally #[repr(transparent)]
    // wraps a [u8]
    core::mem::transmute::<&[u8], &ReadableProcessSlice>(
        raw_processbuf_to_nonnul(ptr, len).as_ref(),
    )
}

/// Convert an process buffers's internal representation to a
/// [`WriteableProcessSlice`].
///
/// This function will automatically convert zero-length process
/// buffers into valid zero-sized Rust slices regardless of the value
/// of `ptr`.
///
/// # Safety requirements
///
/// In the case of `len != 0`, the memory `[ptr; ptr + len)` must be
/// within a single process' address space, and `ptr` must be
/// nonzero. This memory region must be mapped as _readable_ and
/// _writable_, and optionally _executable_. It must be allocated
/// within a single process' address space for the entire lifetime
/// `'a`.
///
/// No other mutable or immutable Rust reference pointing to an
/// overlapping memory region, which is not also created over
/// `UnsafeCell`, may exist over the entire lifetime `'a`. Even though
/// this effectively returns a slice of [`Cell`]s, writing to some
/// memory through a [`Cell`] while another reference is in scope is
/// unsound. Because a process is free to modify its memory, this is
/// -- in a broader sense -- true for all process memory.
///
/// However, it is sound for multiple overlapping
/// [`ReadableProcessSlice`]s or [`WriteableProcessSlice`]s to be in
/// scope at the same time.
pub unsafe fn raw_processbuf_to_rwprocessslice<'a>(
    ptr: *mut u8,
    len: usize,
) -> &'a WriteableProcessSlice {
    // Transmute a reference to a slice of Cell<u8>s into a reference
    // to a ReadableProcessSlice. This is possible as
    // ReadableProcessSlice is a #[repr(transparent)] wrapper around a
    // [ReadableProcessByte], which is a #[repr(transparent)] wrapper
    // around a [Cell<u8>], which is a #[repr(transparent)] wrapper
    // around an [UnsafeCell<u8>], which finally #[repr(transparent)]
    // wraps a [u8]
    core::mem::transmute::<&[u8], &WriteableProcessSlice>(
        // Rust has very strict requirements on pointer validity[1]
        // which also in part apply to accesses of length 0. We allow
        // an application to supply arbitrary pointers if the buffer
        // length is 0, but this is not allowed for Rust slices. For
        // instance, a null pointer is _never_ valid, not even for
        // accesses of size zero.
        //
        // To get a pointer which does not point to valid (allocated)
        // memory, but is safe to construct for accesses of size zero,
        // we must call NonNull::dangling(). The resulting pointer is
        // guaranteed to be well-aligned and uphold the guarantees
        // required for accesses of size zero.
        //
        // [1]: https://doc.rust-lang.org/core/ptr/index.html#safety
        match len {
            0 => core::slice::from_raw_parts_mut(core::ptr::NonNull::<u8>::dangling().as_ptr(), 0),
            _ => core::slice::from_raw_parts_mut(ptr, len),
        },
    )
}

/// A readable region of userspace process memory.
///
/// This trait can be used to gain read-only access to memory regions
/// wrapped in either a [`ReadOnlyProcessBuffer`] or a
/// [`ReadWriteProcessBuffer`] type.
pub trait ReadableProcessBuffer {
    /// Length of the memory region.
    ///
    /// If the process is no longer alive and the memory has been
    /// reclaimed, this method must return 0.
    ///
    /// # Default Process Buffer
    ///
    /// A default instance of a process buffer must return 0.
    fn len(&self) -> usize;

    /// Pointer to the first byte of the userspace memory region.
    ///
    /// If the length of the initially shared memory region
    /// (irrespective of the return value of
    /// [`len`](ReadableProcessBuffer::len)) is 0, this function returns
    /// a pointer to address `0x0`. This is because processes may
    /// allow buffers with length 0 to share no memory with the
    /// kernel. Because these buffers have zero length, they may have
    /// any pointer value. However, these _dummy addresses_ should not
    /// be leaked, so this method returns 0 for zero-length slices.
    ///
    /// # Default Process Buffer
    ///
    /// A default instance of a process buffer must return a pointer
    /// to address `0x0`.
    fn ptr(&self) -> *const u8;

    /// Get the pointer as a raw slice ref
    fn slice(&self) -> *const [u8] {
        core::ptr::slice_from_raw_parts(self.ptr(), self.len())
    }

    /// Applies a function to the (read only) process slice reference
    /// pointed to by the process buffer.
    ///
    /// If the process is no longer alive and the memory has been
    /// reclaimed, this method must return
    /// `Err(process::Error::NoSuchApp)`.
    ///
    /// # Default Process Buffer
    ///
    /// A default instance of a process buffer must return
    /// `Err(process::Error::NoSuchApp)` without executing the passed
    /// closure.
    fn enter<F, R>(&self, fun: F) -> Result<R, process::Error>
    where
        F: FnOnce(&ReadableProcessSlice) -> R;
}

/// A readable and writeable region of userspace process memory.
///
/// This trait can be used to gain read-write access to memory regions
/// wrapped in a [`ReadWriteProcessBuffer`].
///
/// This is a supertrait of [`ReadableProcessBuffer`], which features
/// methods allowing mutable access.
pub trait WriteableProcessBuffer: ReadableProcessBuffer {
    /// Applies a function to the mutable process slice reference
    /// pointed to by the [`ReadWriteProcessBuffer`].
    ///
    /// If the process is no longer alive and the memory has been
    /// reclaimed, this method must return
    /// `Err(process::Error::NoSuchApp)`.
    ///
    /// # Default Process Buffer
    ///
    /// A default instance of a process buffer must return
    /// `Err(process::Error::NoSuchApp)` without executing the passed
    /// closure.
    fn mut_enter<F, R>(&self, fun: F) -> Result<R, process::Error>
    where
        F: FnOnce(&WriteableProcessSlice) -> R;
}

/// Read-only buffer shared by a userspace process.
///
/// This struct is provided to capsules when a process `allow`s a
/// particular section of its memory to the kernel and gives the
/// kernel read access to this memory.
///
/// It can be used to obtain a [`ReadableProcessSlice`], which is
/// based around a slice of [`Cell`]s. This is because a userspace can
/// `allow` overlapping sections of memory into different
/// [`ReadableProcessSlice`]. Having at least one mutable Rust slice
/// along with read-only slices to overlapping memory in Rust violates
/// Rust's aliasing rules. A slice of [`Cell`]s avoids this issue by
/// explicitly supporting interior mutability. Still, a memory barrier
/// prior to switching to userspace is required, as the compiler is
/// free to reorder reads and writes, even through [`Cell`]s.
pub struct ReadOnlyProcessBuffer {
    ptr: *const u8,
    len: usize,
    process_id: Option<ProcessId>,
}

impl ReadOnlyProcessBuffer {
    /// Construct a new [`ReadOnlyProcessBuffer`] over a given pointer and
    /// length.
    ///
    /// # Safety requirements
    ///
    /// Refer to the safety requirements of
    /// [`ReadOnlyProcessBuffer::new_external`].
    pub(crate) unsafe fn new(ptr: *const u8, len: usize, process_id: ProcessId) -> Self {
        ReadOnlyProcessBuffer {
            ptr,
            len,
            process_id: Some(process_id),
        }
    }

    /// Same as new() but takes an option of a process ID
    /// If none, then the buffer is always invalid.
    pub(crate) unsafe fn new_option(
        ptr: *const u8,
        len: usize,
        process_id: Option<ProcessId>,
    ) -> Self {
        ReadOnlyProcessBuffer {
            ptr,
            len,
            process_id,
        }
    }

    /// Construct a new [`ReadOnlyProcessBuffer`] over a given pointer
    /// and length.
    ///
    /// Publicly accessible constructor, which requires the
    /// [`capabilities::ExternalProcessCapability`] capability. This
    /// is provided to allow implementations of the
    /// [`Process`](crate::process::Process) trait outside of the
    /// `kernel` crate.
    ///
    /// # Safety requirements
    ///
    /// If the length is `0`, an arbitrary pointer may be passed into
    /// `ptr`. It does not necessarily have to point to allocated
    /// memory, nor does it have to meet [Rust's pointer validity
    /// requirements](https://doc.rust-lang.org/core/ptr/index.html#safety).
    /// [`ReadOnlyProcessBuffer`] must ensure that all Rust slices
    /// with a length of `0` must be constructed over a valid (but not
    /// necessarily allocated) base pointer.
    ///
    /// If the length is not `0`, the memory region of `[ptr; ptr +
    /// len)` must be valid memory of the process of the given
    /// [`ProcessId`]. It must be allocated and and accessible over
    /// the entire lifetime of the [`ReadOnlyProcessBuffer`]. It must
    /// not point to memory outside of the process' accessible memory
    /// range, or point (in part) to other processes or kernel
    /// memory. The `ptr` must meet [Rust's requirements for pointer
    /// validity](https://doc.rust-lang.org/core/ptr/index.html#safety),
    /// in particular it must have a minimum alignment of
    /// `core::mem::align_of::<u8>()` on the respective platform. It
    /// must point to memory mapped as _readable_ and optionally
    /// _writable_ and _executable_.
    /// On a CHERI platform there are additional requirements that
    /// that the process had a valid capability for the span
    /// indicated by the combination of ptr and len.
    pub unsafe fn new_external(
        ptr: *const u8,
        len: usize,
        process_id: ProcessId,
        _cap: &dyn capabilities::ExternalProcessCapability,
    ) -> Self {
        Self::new(ptr, len, process_id)
    }

    /// Consumes the ReadOnlyProcessBuffer, returning its constituent
    /// pointer and size. This ensures that there cannot
    /// simultaneously be both a `ReadOnlyProcessBuffer` and a pointer
    /// to its internal data.
    ///
    /// `consume` can be used when the kernel needs to pass the
    /// underlying values across the kernel-to-user boundary (e.g., in
    /// return values to system calls).
    pub(crate) fn consume(self) -> (*const u8, usize, Option<ProcessId>) {
        (self.ptr, self.len, self.process_id)
    }
}

impl ReadableProcessBuffer for ReadOnlyProcessBuffer {
    /// Return the length of the buffer in bytes.
    fn len(&self) -> usize {
        self.process_id
            .map_or(0, |pid| pid.kernel.process_map_or(0, pid, |_| self.len))
    }

    /// Return the pointer to the start of the buffer.
    fn ptr(&self) -> *const u8 {
        if self.len == 0 {
            core::ptr::null::<u8>()
        } else {
            self.ptr
        }
    }

    /// Access the contents of the buffer in a closure.
    ///
    /// This verifies the process is still valid before accessing the underlying
    /// memory.
    fn enter<F, R>(&self, fun: F) -> Result<R, process::Error>
    where
        F: FnOnce(&ReadableProcessSlice) -> R,
    {
        match self.process_id {
            None => Err(process::Error::NoSuchApp),
            Some(pid) => pid
                .kernel
                .process_map_or(Err(process::Error::NoSuchApp), pid, |_| {
                    // Safety: `kernel.process_map_or()` validates that
                    // the process still exists and its memory is still
                    // valid. In particular, `Process` tracks the "high water
                    // mark" of memory that the process has `allow`ed to the
                    // kernel. Because `Process` does not feature an API to
                    // move the "high water mark" down again, which would be
                    // called once a `ProcessBuffer` has been passed back into
                    // the kernel, a given `Process` implementation must assume
                    // that the memory described by a once-allowed
                    // `ProcessBuffer` is still in use, and thus will not
                    // permit the process to free any memory after it has
                    // been `allow`ed to the kernel once. This guarantees
                    // that the buffer is safe to convert into a slice
                    // here. For more information, refer to the
                    // comment and subsequent discussion on tock/tock#2632:
                    // https://github.com/tock/tock/pull/2632#issuecomment-869974365
                    Ok(fun(unsafe {
                        raw_processbuf_to_roprocessslice(self.ptr, self.len)
                    }))
                }),
        }
    }
}

impl Default for ReadOnlyProcessBuffer {
    fn default() -> Self {
        ReadOnlyProcessBuffer {
            ptr: core::ptr::null_mut::<u8>(),
            len: 0,
            process_id: None,
        }
    }
}

/// Provides access to a [`ReadOnlyProcessBuffer`] with a restricted lifetime.
/// This automatically dereferences into a ReadOnlyProcessBuffer
pub struct ReadOnlyProcessBufferRef<'a> {
    buf: ReadOnlyProcessBuffer,
    _phantom: PhantomData<&'a ()>,
}

impl<'a> ReadOnlyProcessBufferRef<'a> {
    /// Construct a new [`ReadOnlyProcessBufferRef`] over a given pointer and
    /// length with a lifetime derived from the caller.
    ///
    /// # Safety requirements
    ///
    /// Refer to the safety requirements of
    /// [`ReadOnlyProcessBuffer::new_external`]. The derived lifetime can
    /// help enforce the invariant that this incoming pointer may only
    /// be access for a certain duration.
    pub(crate) unsafe fn new(ptr: *const u8, len: usize, process_id: ProcessId) -> Self {
        Self {
            buf: ReadOnlyProcessBuffer::new(ptr, len, process_id),
            _phantom: PhantomData,
        }
    }
}

impl Deref for ReadOnlyProcessBufferRef<'_> {
    type Target = ReadOnlyProcessBuffer;
    fn deref(&self) -> &Self::Target {
        &self.buf
    }
}

/// Read-writable buffer shared by a userspace process.
///
/// This struct is provided to capsules when a process `allows` a
/// particular section of its memory to the kernel and gives the
/// kernel read and write access to this memory.
///
/// It can be used to obtain a [`WriteableProcessSlice`], which is
/// based around a slice of [`Cell`]s. This is because a userspace can
/// `allow` overlapping sections of memory into different
/// [`WriteableProcessSlice`]. Having at least one mutable Rust slice
/// along with read-only or other mutable slices to overlapping memory
/// in Rust violates Rust's aliasing rules. A slice of [`Cell`]s
/// avoids this issue by explicitly supporting interior
/// mutability. Still, a memory barrier prior to switching to
/// userspace is required, as the compiler is free to reorder reads
/// and writes, even through [`Cell`]s.
pub struct ReadWriteProcessBuffer {
    ptr: *mut u8,
    len: usize,
    process_id: Option<ProcessId>,
}

/// Implement PartialEq for ease of comparing buffers
impl PartialEq<ReadableProcessByte> for ReadableProcessByte {
    fn eq(&self, other: &ReadableProcessByte) -> bool {
        self.cell.get() == other.cell.get()
    }
}

impl PartialEq<u8> for ReadableProcessByte {
    fn eq(&self, other: &u8) -> bool {
        self.cell.get() == *other
    }
}

impl PartialEq<ReadableProcessByte> for u8 {
    fn eq(&self, other: &ReadableProcessByte) -> bool {
        *self == other.cell.get()
    }
}

impl PartialEq<Cell<u8>> for ReadableProcessByte {
    fn eq(&self, other: &Cell<u8>) -> bool {
        self.cell.get() == other.get()
    }
}

impl ReadWriteProcessBuffer {
    /// Construct a new [`ReadWriteProcessBuffer`] over a given
    /// pointer and length.
    ///
    /// # Safety requirements
    ///
    /// Refer to the safety requirements of
    /// [`ReadWriteProcessBuffer::new_external`].
    pub(crate) unsafe fn new(ptr: *mut u8, len: usize, process_id: ProcessId) -> Self {
        ReadWriteProcessBuffer {
            ptr,
            len,
            process_id: Some(process_id),
        }
    }

    /// Construct a new [`ReadWriteProcessBuffer`] over a given
    /// pointer and length.
    ///
    /// Publicly accessible constructor, which requires the
    /// [`capabilities::ExternalProcessCapability`] capability. This
    /// is provided to allow implementations of the
    /// [`Process`](crate::process::Process) trait outside of the
    /// `kernel` crate.
    ///
    /// # Safety requirements
    ///
    /// If the length is `0`, an arbitrary pointer may be passed into
    /// `ptr`. It does not necessarily have to point to allocated
    /// memory, nor does it have to meet [Rust's pointer validity
    /// requirements](https://doc.rust-lang.org/core/ptr/index.html#safety).
    /// [`ReadWriteProcessBuffer`] must ensure that all Rust slices
    /// with a length of `0` must be constructed over a valid (but not
    /// necessarily allocated) base pointer.
    ///
    /// If the length is not `0`, the memory region of `[ptr; ptr +
    /// len)` must be valid memory of the process of the given
    /// [`ProcessId`]. It must be allocated and and accessible over
    /// the entire lifetime of the [`ReadWriteProcessBuffer`]. It must
    /// not point to memory outside of the process' accessible memory
    /// range, or point (in part) to other processes or kernel
    /// memory. The `ptr` must meet [Rust's requirements for pointer
    /// validity](https://doc.rust-lang.org/core/ptr/index.html#safety),
    /// in particular it must have a minimum alignment of
    /// `core::mem::align_of::<u8>()` on the respective platform. It
    /// must point to memory mapped as _readable_ and optionally
    /// _writable_ and _executable_.
    pub unsafe fn new_external(
        ptr: *mut u8,
        len: usize,
        process_id: ProcessId,
        _cap: &dyn capabilities::ExternalProcessCapability,
    ) -> Self {
        Self::new(ptr, len, process_id)
    }

    /// Consumes the ReadWriteProcessBuffer, returning its constituent
    /// pointer and size. This ensures that there cannot
    /// simultaneously be both a `ReadWriteProcessBuffer` and a pointer to
    /// its internal data.
    ///
    /// `consume` can be used when the kernel needs to pass the
    /// underlying values across the kernel-to-user boundary (e.g., in
    /// return values to system calls).
    pub(crate) fn consume(self) -> (*mut u8, usize, Option<ProcessId>) {
        (self.ptr, self.len, self.process_id)
    }

    /// This is a `const` version of `Default::default` with the same
    /// semantics.
    ///
    /// Having a const initializer allows initializing a fixed-size
    /// array with default values without the struct being marked
    /// `Copy` as such:
    ///
    /// ```
    /// use kernel::processbuffer::ReadWriteProcessBuffer;
    /// const DEFAULT_RWPROCBUF_VAL: ReadWriteProcessBuffer
    ///     = ReadWriteProcessBuffer::const_default();
    /// let my_array = [DEFAULT_RWPROCBUF_VAL; 12];
    /// ```
    pub const fn const_default() -> Self {
        Self {
            ptr: 0x0 as *mut u8,
            len: 0,
            process_id: None,
        }
    }
}

impl ReadableProcessBuffer for ReadWriteProcessBuffer {
    /// Return the length of the buffer in bytes.
    fn len(&self) -> usize {
        self.process_id
            .map_or(0, |pid| pid.kernel.process_map_or(0, pid, |_| self.len))
    }

    /// Return the pointer to the start of the buffer.
    fn ptr(&self) -> *const u8 {
        if self.len == 0 {
            core::ptr::null::<u8>()
        } else {
            self.ptr
        }
    }

    /// Access the contents of the buffer in a closure.
    ///
    /// This verifies the process is still valid before accessing the underlying
    /// memory.
    fn enter<F, R>(&self, fun: F) -> Result<R, process::Error>
    where
        F: FnOnce(&ReadableProcessSlice) -> R,
    {
        match self.process_id {
            None => Err(process::Error::NoSuchApp),
            Some(pid) => pid
                .kernel
                .process_map_or(Err(process::Error::NoSuchApp), pid, |_| {
                    // Safety: `kernel.process_map_or()` validates that
                    // the process still exists and its memory is still
                    // valid. In particular, `Process` tracks the "high water
                    // mark" of memory that the process has `allow`ed to the
                    // kernel. Because `Process` does not feature an API to
                    // move the "high water mark" down again, which would be
                    // called once a `ProcessBuffer` has been passed back into
                    // the kernel, a given `Process` implementation must assume
                    // that the memory described by a once-allowed
                    // `ProcessBuffer` is still in use, and thus will not
                    // permit the process to free any memory after it has
                    // been `allow`ed to the kernel once. This guarantees
                    // that the buffer is safe to convert into a slice
                    // here. For more information, refer to the
                    // comment and subsequent discussion on tock/tock#2632:
                    // https://github.com/tock/tock/pull/2632#issuecomment-869974365
                    Ok(fun(unsafe {
                        raw_processbuf_to_roprocessslice(self.ptr, self.len)
                    }))
                }),
        }
    }
}

impl WriteableProcessBuffer for ReadWriteProcessBuffer {
    fn mut_enter<F, R>(&self, fun: F) -> Result<R, process::Error>
    where
        F: FnOnce(&WriteableProcessSlice) -> R,
    {
        match self.process_id {
            None => Err(process::Error::NoSuchApp),
            Some(pid) => pid
                .kernel
                .process_map_or(Err(process::Error::NoSuchApp), pid, |_| {
                    // Safety: `kernel.process_map_or()` validates that
                    // the process still exists and its memory is still
                    // valid. In particular, `Process` tracks the "high water
                    // mark" of memory that the process has `allow`ed to the
                    // kernel. Because `Process` does not feature an API to
                    // move the "high water mark" down again, which would be
                    // called once a `ProcessBuffer` has been passed back into
                    // the kernel, a given `Process` implementation must assume
                    // that the memory described by a once-allowed
                    // `ProcessBuffer` is still in use, and thus will not
                    // permit the process to free any memory after it has
                    // been `allow`ed to the kernel once. This guarantees
                    // that the buffer is safe to convert into a slice
                    // here. For more information, refer to the
                    // comment and subsequent discussion on tock/tock#2632:
                    // https://github.com/tock/tock/pull/2632#issuecomment-869974365
                    Ok(fun(unsafe {
                        raw_processbuf_to_rwprocessslice(self.ptr, self.len)
                    }))
                }),
        }
    }
}

impl Default for ReadWriteProcessBuffer {
    fn default() -> Self {
        Self::const_default()
    }
}

/// Provides access to a [`ReadWriteProcessBuffer`] with a restricted lifetime.
/// This automatically dereferences into a ReadWriteProcessBuffer
pub struct ReadWriteProcessBufferRef<'a> {
    buf: ReadWriteProcessBuffer,
    _phantom: PhantomData<&'a ()>,
}

impl<'a> ReadWriteProcessBufferRef<'a> {
    /// Construct a new [`ReadWriteProcessBufferRef`] over a given pointer and
    /// length with a lifetime derived from the caller.
    ///
    /// # Safety requirements
    ///
    /// Refer to the safety requirements of
    /// [`ReadWriteProcessBuffer::new_external`]. The derived lifetime can
    /// help enforce the invariant that this incoming pointer may only
    /// be access for a certain duration.
    pub(crate) unsafe fn new(ptr: *mut u8, len: usize, process_id: ProcessId) -> Self {
        Self {
            buf: ReadWriteProcessBuffer::new(ptr, len, process_id),
            _phantom: PhantomData,
        }
    }
}

impl Deref for ReadWriteProcessBufferRef<'_> {
    type Target = ReadWriteProcessBuffer;
    fn deref(&self) -> &Self::Target {
        &self.buf
    }
}

/// A shareable region of userspace memory.
///
/// This trait can be used to gain read-write access to memory regions
/// wrapped in a ProcessBuffer type.
// We currently don't need any special functionality in the kernel for this
// type so we alias it as `ReadWriteProcessBuffer`.
pub type UserspaceReadableProcessBuffer = ReadWriteProcessBuffer;

/// Read-only wrapper around a [`Cell`]
///
/// This type is used in providing the [`ReadableProcessSlice`]. The
/// memory over which a [`ReadableProcessSlice`] exists must never be
/// written to by the kernel. However, it may either exist in flash
/// (read-only memory) or RAM (read-writeable memory). Consequently, a
/// process may `allow` memory overlapping with a
/// [`ReadOnlyProcessBuffer`] also simultaneously through a
/// [`ReadWriteProcessBuffer`]. Hence, the kernel can have two
/// references to the same memory, where one can lead to mutation of
/// the memory contents. Therefore, the kernel must use [`Cell`]s
/// around the bytes shared with userspace, to avoid violating Rust's
/// aliasing rules.
///
/// This read-only wrapper around a [`Cell`] only exposes methods
/// which are safe to call on a process-shared read-only `allow`
/// memory.
///
/// Because userspace might choose to arbitrarily mutate the contents there is another bound
/// required that every bit pattern be valid for the type. This is true for integers and
/// compositions of them. It is not true for enums. We might add a marker for this and a derive
/// macro, but for now we will just not give ways of constructing anything but integer versions
#[repr(transparent)]
pub struct ReadableProcessT<T: Copy> {
    cell: Cell<T>,
}

pub type ReadableProcessByte = ReadableProcessT<u8>;
pub type ReadableProcessU32 = ReadableProcessT<u32>;

impl<T: Copy> ReadableProcessT<T> {
    #[inline]
    pub fn get(&self) -> T {
        self.cell.get()
    }
}

/// Readable and accessible slice of memory of a process buffer.
///
///
/// The only way to obtain this struct is through a
/// [`ReadWriteProcessBuffer`] or [`ReadOnlyProcessBuffer`].
///
/// Slices provide a more convenient, traditional interface to process
/// memory. These slices are transient, as the underlying buffer must
/// be checked each time a slice is created. This is usually enforced
/// by the anonymous lifetime defined by the creation of the slice.
#[repr(transparent)]
pub struct ReadableProcessSlice {
    slice: [ReadableProcessByte],
}

impl<'a> const Default for &'a ReadableProcessSlice {
    fn default() -> Self {
        let slice: &[ReadableProcessByte] = [].as_slice();
        slice.into()
    }
}

impl<'a> const From<&'a [ReadableProcessByte]> for &'a ReadableProcessSlice {
    fn from(slice: &'a [ReadableProcessByte]) -> Self {
        // As ReadableProcessSlice is a transparent wrapper around its inner type,
        // [ReadableProcessByte], we can safely transmute a reference to the inner
        // type as a reference to the outer type with the same lifetime.
        unsafe { core::mem::transmute::<&[ReadableProcessByte], &ReadableProcessSlice>(slice) }
    }
}

impl<'a> const From<&'a mut [ReadableProcessByte]> for &'a mut ReadableProcessSlice {
    fn from(slice: &'a mut [ReadableProcessByte]) -> Self {
        // Same justification as non-mut version.
        unsafe {
            core::mem::transmute::<&mut [ReadableProcessByte], &mut ReadableProcessSlice>(slice)
        }
    }
}

impl<'a> const From<&'a ReadableProcessSlice> for &'a [ReadableProcessByte] {
    fn from(value: &'a ReadableProcessSlice) -> Self {
        &value.slice
    }
}

impl PartialEq for ReadableProcessSlice {
    fn eq(&self, other: &Self) -> bool {
        self.slice == other.slice
    }
}

const fn cast_byte_slice_to_process_slice(
    byte_slice: &[ReadableProcessByte],
) -> &ReadableProcessSlice {
    byte_slice.into()
}

// Allow a u8 slice to be viewed as a ReadableProcessSlice to allow client code
// to be authored once and accept either [u8] or ReadableProcessSlice.
impl<'a> const From<&'a [u8]> for &'a ReadableProcessSlice {
    fn from(val: &'a [u8]) -> Self {
        // # Safety
        //
        // The layout of a [u8] and ReadableProcessSlice are guaranteed to be
        // the same. This also extends the lifetime of the buffer, so aliasing
        // rules are thus maintained properly.
        unsafe { core::mem::transmute(val) }
    }
}

// Allow a mutable u8 slice to be viewed as a ReadableProcessSlice to allow
// client code to be authored once and accept either [u8] or
// ReadableProcessSlice.
impl<'a> const From<&'a mut [u8]> for &'a ReadableProcessSlice {
    fn from(val: &'a mut [u8]) -> Self {
        // # Safety
        //
        // The layout of a [u8] and ReadableProcessSlice are guaranteed to be
        // the same. This also extends the mutable lifetime of the buffer, so
        // aliasing rules are thus maintained properly.
        unsafe { core::mem::transmute(val) }
    }
}

impl ReadableProcessSlice {
    /// Safe wrapper that aligns a ReadableProcessSlice
    #[inline]
    pub fn align_to_u32(
        &self,
    ) -> (
        &ReadableProcessSlice,
        &[ReadableProcessU32],
        &ReadableProcessSlice,
    ) {
        unsafe {
            // Safety: all (aligned) groups of 4 ReadableProcessBytes are a ReadableProcessU32
            let (l, m, r) = self.slice.align_to();
            (l.into(), m, r.into())
        }
    }

    /// Copy the contents of a [`ReadableProcessSlice`] into a mutable
    /// slice reference.
    ///
    /// The length of `self` must be the same as `dest`. Subslicing
    /// can be used to obtain a slice of matching length.
    ///
    /// # Panics
    ///
    /// This function will panic if `self.len() != dest.len()`.
    pub fn copy_to_slice(&self, dest: &mut [u8]) {
        // The panic code path was put into a cold function to not
        // bloat the call site.
        #[inline(never)]
        #[cold]
        #[track_caller]
        fn len_mismatch_fail(dst_len: usize, src_len: usize) -> ! {
            panic!(
                "source slice length ({}) does not match destination slice length ({})",
                src_len, dst_len,
            );
        }

        if self.copy_to_slice_or_err(dest).is_err() {
            len_mismatch_fail(dest.len(), self.len());
        }
    }

    /// Copy the contents of a [`ReadableProcessSlice`] into a mutable
    /// slice reference.
    ///
    /// The length of `self` must be the same as `dest`. Subslicing
    /// can be used to obtain a slice of matching length.
    pub fn copy_to_slice_or_err(&self, dest: &mut [u8]) -> Result<(), ErrorCode> {
        // Method implemetation adopted from the
        // core::slice::copy_from_slice method implementation:
        // https://doc.rust-lang.org/src/core/slice/mod.rs.html#3034-3036

        if self.len() != dest.len() {
            Err(ErrorCode::SIZE)
        } else {
            // _If_ this turns out to not be efficiently optimized, it
            // should be possible to use a ptr::copy_nonoverlapping here
            // given we have exclusive mutable access to the destination
            // slice which will never be in process memory, and the layout
            // of &[ReadableProcessByte] is guaranteed to be compatible to
            // &[u8].
            for (i, b) in self.slice.iter().enumerate() {
                dest[i] = b.get();
            }
            Ok(())
        }
    }

    /// Return the length of the slice in bytes.
    pub fn len(&self) -> usize {
        self.slice.len()
    }

    /// Return an iterator over the bytes of the slice.
    pub fn iter(&self) -> core::slice::Iter<'_, ReadableProcessByte> {
        self.slice.iter()
    }

    /// Iterate the slice in chunks.
    pub fn chunks(
        &self,
        chunk_size: usize,
    ) -> impl core::iter::Iterator<Item = &ReadableProcessSlice> {
        self.slice
            .chunks(chunk_size)
            .map(cast_byte_slice_to_process_slice)
    }

    /// Access a portion of the slice with bounds checking. If the access is not
    /// within the slice then `None` is returned.
    pub fn get(&self, range: Range<usize>) -> Option<&ReadableProcessSlice> {
        if let Some(slice) = self.slice.get(range) {
            Some(cast_byte_slice_to_process_slice(slice))
        } else {
            None
        }
    }

    /// Access a portion of the slice with bounds checking. If the access is not
    /// within the slice then `None` is returned.
    pub fn get_from(&self, range: RangeFrom<usize>) -> Option<&ReadableProcessSlice> {
        if let Some(slice) = self.slice.get(range) {
            Some(cast_byte_slice_to_process_slice(slice))
        } else {
            None
        }
    }

    /// Access a portion of the slice with bounds checking. If the access is not
    /// within the slice then `None` is returned.
    pub fn get_to(&self, range: RangeTo<usize>) -> Option<&ReadableProcessSlice> {
        if let Some(slice) = self.slice.get(range) {
            Some(cast_byte_slice_to_process_slice(slice))
        } else {
            None
        }
    }
}

impl<'a> IntoIterator for &'a ReadableProcessSlice {
    type IntoIter = core::slice::Iter<'a, ReadableProcessByte>;
    type Item = <Self::IntoIter as Iterator>::Item;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub type WriteableProcessT<T> = Cell<T>;
pub type WriteableProcessByte = WriteableProcessT<u8>;
pub type WriteableProcessU32 = WriteableProcessT<u32>;

/// Read-writeable and accessible slice of memory of a process buffer
///
/// The only way to obtain this struct is through a
/// [`ReadWriteProcessBuffer`].
///
/// Slices provide a more convenient, traditional interface to process
/// memory. These slices are transient, as the underlying buffer must
/// be checked each time a slice is created. This is usually enforced
/// by the anonymous lifetime defined by the creation of the slice.
#[repr(transparent)]
pub struct WriteableProcessSlice {
    slice: [Cell<u8>],
}

impl<'a> const From<&'a [Cell<u8>]> for &'a WriteableProcessSlice {
    fn from(cell_slice: &'a [Cell<u8>]) -> Self {
        // # Safety
        //
        // As WriteableProcessSlice is a transparent wrapper around its inner type,
        // [Cell<u8>], we can safely transmute a reference to the inner type as the
        // outer type with the same lifetime.
        unsafe { core::mem::transmute(cell_slice) }
    }
}

impl<'a> const From<&'a mut [Cell<u8>]> for &'a mut WriteableProcessSlice {
    fn from(cell_slice: &'a mut [Cell<u8>]) -> Self {
        // # Safety
        // Same as non-mut version
        unsafe { core::mem::transmute(cell_slice) }
    }
}

impl<'a> const From<&'a mut WriteableProcessSlice> for &'a mut [Cell<u8>] {
    fn from(value: &'a mut WriteableProcessSlice) -> Self {
        &mut value.slice
    }
}

fn cast_cell_slice_to_process_slice(cell_slice: &[Cell<u8>]) -> &WriteableProcessSlice {
    cell_slice.into()
}

// Allow a mutable u8 slice to be viewed as a WritableProcessSlice to allow
// client code to be authored once and accept either [u8] or
// WriteableProcessSlice.
impl<'a> const From<&'a mut [u8]> for &'a WriteableProcessSlice {
    fn from(val: &'a mut [u8]) -> Self {
        // # Safety
        //
        // The layout of a [u8] and WriteableProcessSlice are guaranteed to be
        // the same. This also extends the mutable lifetime of the buffer, so
        // aliasing rules are thus maintained properly.
        unsafe { core::mem::transmute(val) }
    }
}

impl WriteableProcessSlice {
    /// Safe wrapper that aligns a WriteableProcessSlice
    #[inline]
    pub fn align_to_u32(
        &self,
    ) -> (
        &WriteableProcessSlice,
        &[WriteableProcessU32],
        &WriteableProcessSlice,
    ) {
        unsafe {
            // Safety: all (aligned) groups of 4 WriteableProcessBytes are a WriteableProcessU32
            let (l, m, r) = self.slice.align_to();
            (l.into(), m, r.into())
        }
    }

    /// Copy the contents of a [`WriteableProcessSlice`] into a mutable
    /// slice reference.
    ///
    /// The length of `self` must be the same as `dest`. Subslicing
    /// can be used to obtain a slice of matching length.
    ///
    /// # Panics
    ///
    /// This function will panic if `self.len() != dest.len()`.
    pub fn copy_to_slice(&self, dest: &mut [u8]) {
        // The panic code path was put into a cold function to not
        // bloat the call site.
        #[inline(never)]
        #[cold]
        #[track_caller]
        fn len_mismatch_fail(dst_len: usize, src_len: usize) -> ! {
            panic!(
                "source slice length ({}) does not match destination slice length ({})",
                src_len, dst_len,
            );
        }

        if self.copy_to_slice_or_err(dest).is_err() {
            len_mismatch_fail(dest.len(), self.len());
        }
    }

    /// Copy the contents of a [`WriteableProcessSlice`] into a mutable
    /// slice reference.
    ///
    /// The length of `self` must be the same as `dest`. Subslicing
    /// can be used to obtain a slice of matching length.
    pub fn copy_to_slice_or_err(&self, dest: &mut [u8]) -> Result<(), ErrorCode> {
        // Method implemetation adopted from the
        // core::slice::copy_from_slice method implementation:
        // https://doc.rust-lang.org/src/core/slice/mod.rs.html#3034-3036

        if self.len() != dest.len() {
            Err(ErrorCode::SIZE)
        } else {
            // _If_ this turns out to not be efficiently optimized, it
            // should be possible to use a ptr::copy_nonoverlapping here
            // given we have exclusive mutable access to the destination
            // slice which will never be in process memory, and the layout
            // of &[Cell<u8>] is guaranteed to be compatible to &[u8].
            self.slice
                .iter()
                .zip(dest.iter_mut())
                .for_each(|(src, dst)| *dst = src.get());
            Ok(())
        }
    }

    /// Copy the contents of a slice of bytes into a [`WriteableProcessSlice`].
    ///
    /// The length of `src` must be the same as `self`. Subslicing can
    /// be used to obtain a slice of matching length.
    ///
    /// # Panics
    ///
    /// This function will panic if `src.len() != self.len()`.
    pub fn copy_from_slice(&self, src: &[u8]) {
        // Method implemetation adopted from the
        // core::slice::copy_from_slice method implementation:
        // https://doc.rust-lang.org/src/core/slice/mod.rs.html#3034-3036

        // The panic code path was put into a cold function to not
        // bloat the call site.
        #[inline(never)]
        #[cold]
        #[track_caller]
        fn len_mismatch_fail(dst_len: usize, src_len: usize) -> ! {
            panic!(
                "src slice len ({}) != dest slice len ({})",
                src_len, dst_len,
            );
        }

        if self.copy_from_slice_or_err(src).is_err() {
            len_mismatch_fail(self.len(), src.len());
        }
    }

    /// Copy the contents of a slice of bytes into a [`WriteableProcessSlice`].
    ///
    /// The length of `src` must be the same as `self`. Subslicing can
    /// be used to obtain a slice of matching length.
    pub fn copy_from_slice_or_err(&self, src: &[u8]) -> Result<(), ErrorCode> {
        // Method implemetation adopted from the
        // core::slice::copy_from_slice method implementation:
        // https://doc.rust-lang.org/src/core/slice/mod.rs.html#3034-3036

        if self.len() != src.len() {
            Err(ErrorCode::SIZE)
        } else {
            // _If_ this turns out to not be efficiently optimized, it
            // should be possible to use a ptr::copy_nonoverlapping here
            // given we have exclusive mutable access to the destination
            // slice which will never be in process memory, and the layout
            // of &[Cell<u8>] is guaranteed to be compatible to &[u8].
            src.iter()
                .zip(self.slice.iter())
                .for_each(|(src, dst)| dst.set(*src));
            Ok(())
        }
    }

    /// Return the length of the slice in bytes.
    pub fn len(&self) -> usize {
        self.slice.len()
    }

    /// Return an iterator over the slice.
    pub fn iter(&self) -> core::slice::Iter<'_, Cell<u8>> {
        self.slice.iter()
    }

    /// Iterate over the slice in chunks.
    pub fn chunks(
        &self,
        chunk_size: usize,
    ) -> impl core::iter::Iterator<Item = &WriteableProcessSlice> {
        self.slice
            .chunks(chunk_size)
            .map(cast_cell_slice_to_process_slice)
    }

    /// Access a portion of the slice with bounds checking. If the access is not
    /// within the slice then `None` is returned.
    pub fn get(&self, range: Range<usize>) -> Option<&WriteableProcessSlice> {
        if let Some(slice) = self.slice.get(range) {
            Some(cast_cell_slice_to_process_slice(slice))
        } else {
            None
        }
    }

    /// Access a portion of the slice with bounds checking. If the access is not
    /// within the slice then `None` is returned.
    pub fn get_from(&self, range: RangeFrom<usize>) -> Option<&WriteableProcessSlice> {
        if let Some(slice) = self.slice.get(range) {
            Some(cast_cell_slice_to_process_slice(slice))
        } else {
            None
        }
    }

    /// Access a portion of the slice with bounds checking. If the access is not
    /// within the slice then `None` is returned.
    pub fn get_to(&self, range: RangeTo<usize>) -> Option<&WriteableProcessSlice> {
        if let Some(slice) = self.slice.get(range) {
            Some(cast_cell_slice_to_process_slice(slice))
        } else {
            None
        }
    }
}

impl<'a> IntoIterator for &'a WriteableProcessSlice {
    type IntoIter = core::slice::Iter<'a, Cell<u8>>;
    type Item = <Self::IntoIter as Iterator>::Item;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// ReadableProcessSlice and WriteableProcessSlice are just wrappers around a slice, and have the
/// same sub-slicing semantics as the type they wrap.
/// To avoid so much boilerplate in indexing the process slices this macro will generates an
/// implementation of a trait.
/// Deref also exposes slices, and combined with Into it is questionable why we need these at all.
macro_rules! DeriveSliceIndexForHelper {
    ($s : ident, $field : ident, $trait : ident, $trait_type : ty, $f : ident, $self_ref : ty, $out_ref : ty, $($output : ty)?) => {
        impl $trait<$trait_type> for $s {
            $(type Output = $output;)?
            fn $f(self : $self_ref, idx : $trait_type) -> $out_ref {
                self.$field.$f(idx).into()
            }
        }
    };
}

/// Implement the normal suite of index operations.
macro_rules! DeriveSliceIndexFor {
    ($s : ident, $field : ident, $t : ty) => {
        DeriveSliceIndexForHelper!($s, $field, Index, usize, index, &Self, &$t, $t);
        DeriveSliceIndexForHelper!($s, $field, Index, Range<usize>, index, &Self, &Self, Self);
        DeriveSliceIndexForHelper!($s, $field, Index, RangeTo<usize>, index, &Self, &Self, Self);
        DeriveSliceIndexForHelper!(
            $s,
            $field,
            Index,
            RangeFrom<usize>,
            index,
            &Self,
            &Self,
            Self
        );
        // Although we don't currently have a way to obtain exclusive references to these slices,
        // this makes some other traits happy.
        DeriveSliceIndexForHelper!($s, $field, IndexMut, usize, index_mut, &mut Self, &mut $t,);
        DeriveSliceIndexForHelper!(
            $s,
            $field,
            IndexMut,
            Range<usize>,
            index_mut,
            &mut Self,
            &mut Self,
        );
        DeriveSliceIndexForHelper!(
            $s,
            $field,
            IndexMut,
            RangeTo<usize>,
            index_mut,
            &mut Self,
            &mut Self,
        );
        DeriveSliceIndexForHelper!(
            $s,
            $field,
            IndexMut,
            RangeFrom<usize>,
            index_mut,
            &mut Self,
            &mut Self,
        );
    };
}

// Indexing into a WriteableProcessSlice yields a Cell<u8>, as mutating the memory contents is allowed.
DeriveSliceIndexFor!(WriteableProcessSlice, slice, Cell<u8>);
// Indexing into a ReadableProcessSlice must yield a ReadableProcessByte, to limit the API surface
// of the wrapped Cell to read-only operations.
DeriveSliceIndexFor!(ReadableProcessSlice, slice, ReadableProcessByte);

// Impl Deref for the slices to expose the slice methods directly
impl Deref for ReadableProcessSlice {
    type Target = [ReadableProcessByte];

    fn deref(&self) -> &Self::Target {
        &self.slice
    }
}

impl DerefMut for ReadableProcessSlice {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.slice
    }
}

impl Deref for WriteableProcessSlice {
    type Target = [Cell<u8>];

    fn deref(&self) -> &Self::Target {
        &self.slice
    }
}

impl DerefMut for WriteableProcessSlice {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.slice
    }
}

// Allow casting lifelessRefs to inner types.

// Even though not exactly correct, we can cast ReadableProcessSlice to [u8] as lifeless refs are
// for hardware, which doesn't have the same requirements as rust on having mutable references being
// exclusive with immutable ones.
impl misc::divorce::LifelessCastEither<[u8]> for ReadableProcessSlice {
    fn cast_either(value: NonNull<Self>) -> NonNull<[u8]> {
        NonNull::slice_from_raw_parts(value.cast(), (value.as_ptr() as *mut [u8]).len())
    }

    fn cast_back_either(value: NonNull<[u8]>) -> NonNull<Self> {
        // Safety: Cast maintains NonNull-ness
        unsafe { NonNull::new_unchecked(value.as_ptr() as *mut ReadableProcessSlice) }
    }
}

// WriteableProcessSlice can just be unwrapped
impl misc::divorce::LifelessCastEither<[Cell<u8>]> for WriteableProcessSlice {
    fn cast_either(value: NonNull<Self>) -> NonNull<[Cell<u8>]> {
        NonNull::slice_from_raw_parts(value.cast(), (value.as_ptr() as *mut [Cell<u8>]).len())
    }

    fn cast_back_either(value: NonNull<[Cell<u8>]>) -> NonNull<Self> {
        // Safety: Cast maintains NonNull-ness
        unsafe { NonNull::new_unchecked(value.as_ptr() as *mut WriteableProcessSlice) }
    }
}

// WriteableProcessSlice can be unwrapped and drop the cell part
// See comment on ReadableProcessSlice
impl misc::divorce::LifelessCastEither<[u8]> for WriteableProcessSlice {
    fn cast_either(value: NonNull<Self>) -> NonNull<[u8]> {
        NonNull::slice_from_raw_parts(value.cast(), (value.as_ptr() as *mut [u8]).len())
    }

    fn cast_back_either(value: NonNull<[u8]>) -> NonNull<Self> {
        // Safety: Cast maintains NonNull-ness
        unsafe { NonNull::new_unchecked(value.as_ptr() as *mut WriteableProcessSlice) }
    }
}
