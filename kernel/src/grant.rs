//! Support for processes granting memory from their allocations to the kernel.
//!
//!
//!
//! ## Grant Overview
//!
//! Grants allow capsules to dynamically allocate memory from a process to hold
//! state on the process's behalf.
//!
//! Each capsule that wishes to do this needs to have a `Grant` type. `Grant`s
//! are created at boot, and each have a unique ID and a type `T`. This type
//! only allows the capsule to allocate memory from a process in the future. It
//! does not initially represent any allocated memory.
//!
//! When a capsule does wish to use its `Grant` to allocate memory from a
//! process, it must "enter" the `Grant` with a specific `ProcessId`. Entering a
//! `Grant` for a specific process instructs the core kernel to create an object
//! `T` in the process's memory space and provide the capsule with access to it.
//! If the `Grant` has not previously been entered for that process, the memory
//! for object `T` will be allocated from the "grant region" within the
//! kernel-accessible portion of the process's memory.
//!
//! If a `Grant` has never been entered for a process, the object `T` will _not_
//! be allocated in that process's grant region, even if the `Grant` has been
//! entered for other processes.
//!
//! Upcalls and allowed buffer references are stored in the dynamically
//! allocated grant for a particular Driver as well. Upcalls and allowed buffer
//! references are stored outside of the `T` object to enable the kernel to
//! manage them and ensure swapping guarantees are met.
//!
//! The type `T` of a `Grant` is fixed in size and the number of upcalls and
//! allowed buffers associated with a grant is fixed. That is, when a `Grant` is
//! entered for a process the resulting allocated object will be the size of
//! `SizeOf<T>` plus the size for the structure to hold upcalls and allowed
//! buffer references. If capsules need additional process-specific memory for
//! their operation, they can use an `Allocator` to request additional memory
//! from the process's grant region.
//!
//! ```text,ignore
//!                            ┌──────────────────┐
//!                            │                  │
//!                            │ Capsule          │
//!                            │                  │
//!                            └─┬────────────────┘
//!                              │ Capsules hold
//!                              │ references to
//!                              │ grants.
//!                              ▼
//!                            ┌──────────────────┐
//!                            │ Grant            │
//!                            │                  │
//!  Process Memory            │ Type: T          │
//! ┌────────────────────────┐ │ grant_num: 1     │
//! │                        │ │ driver_num: 0x4  │
//! │  ...                   │ └───┬─────────────┬┘
//! ├────────────────────────┤     │Each Grant   │
//! │ Grant       ptr 0      │     │has a pointer│
//! │ Pointers    ptr 1 ───┐ │ ◄───┘per process. │
//! │             ...      │ │                   │
//! │             ptr N    │ │                   │
//! ├──────────────────────┼─┤                   │
//! │  ...                 │ │                   │
//! ├──────────────────────┼─┤                   │
//! │ Grant Region         │ │     When a Grant  │
//! │                      │ │     is allocated  │
//! │ ┌─────────────────┐  │ │     for a process │
//! │ │ Allocated Grant │  │ │ ◄─────────────────┘
//! │ │                 │  │ │     it uses memory
//! │ │  [ SizeOf<T> ]  │  │ │     from the grant
//! │ │─────────────────│  │ │     region.
//! │ │ Padding         │  │ │
//! │ │─────────────────│  │ │
//! │ │ GrantKernelData │  │ │
//! │ └─────────────────┘◄─┘ │
//! │                        │
//! │ ┌─────────────────┐    │
//! │ │ Custom Grant    │    │ ◄── Capsules can
//! │ │                 │    │     allocate extra
//! │ └─────────────────┘    │     memory if needed.
//! │                        │
//! ├─kernel_brk─────────────┤
//! │                        │
//! │ ...                    │
//! └────────────────────────┘
//! ```
//!
//! ## Grant Mechanisms and Types
//!
//! Here is an overview of the types used by grant.rs to implement the Grant
//! functionality in Tock:
//!
//! ```text,ignore
//!                         ┌──────────────────────────┐
//!                         │ struct Grant<T, ...> {   │
//!                         │   driver_num: usize      │
//!                         │   grant_num: usize       │
//!                         │ }                        ├───┐
//! Entering a Grant for a  └──┬───────────────────────┘   │
//! process causes the         │                           │
//! memory for T to be         │ .enter(ProcessId)         │ .enter(ProcessId, fn)
//! allocated.                 ▼                           │
//!                         ┌──────────────────────────┐   │ For convenience,
//! ProcessGrant represents │ struct ProcessGrant<T> { │   │ allocating and getting
//! a Grant allocated for a │   number: usize          │   │ access to the T object
//! specific process.       │   process: &Process      │   │ is combined in one
//!                         │ }                        │   │ .enter() call.
//! A provided closure      └──┬───────────────────────┘   │
//! is given access to         │                           │
//! the underlying memory      │ .enter(fn)                │
//! where the T is stored.     ▼                           │
//!                         ┌────────────────────────────┐ │
//! GrantData wraps the     │ struct GrantData<T>   {    │◄┘
//! type and provides       │   data: &mut T             │
//! mutable access.         │ }                          │
//! GrantKernelData         │ struct GrantKernelData {   │
//! provides access to      │   upcalls: [SavedUpcall]   │
//! scheduling upcalls      │   allow_ro: [SavedAllowRo] │
//! and process buffers.    │   allow_rw: [SavedAllowRW] │
//!                         │ }                          │
//!                         └──┬─────────────────────────┘
//! The actual object T can    │
//! only be accessed inside    │ fn(mem: &GrantData, kernel_data: &GrantKernelData)
//! the closure.               ▼
//! ```

use crate::cheri::CPtrOps;
use core::cell::{Cell, Ref, RefCell, RefMut};
use core::cmp;
use core::convert::Into;
use core::marker::PhantomData;
use core::mem::transmute;
use core::mem::{align_of, size_of};
use core::ops::{Deref, DerefMut};
use core::ptr::{write, NonNull};
use core::slice;
use misc::take_borrow::TakeBorrow;

use crate::collections::list::PanicDeref;
use crate::collections::safe_buf::BufLength;
use crate::config::CONFIG;
use crate::kernel::Kernel;
use crate::process::{Error, Process, ProcessCustomGrantIdentifier, ProcessId};
use crate::processbuffer::{
    raw_processbuf_to_roprocessslice, raw_processbuf_to_rwprocessslice, ReadOnlyProcessBuffer,
    ReadOnlyProcessBufferRef, ReadWriteProcessBuffer, ReadWriteProcessBufferRef,
    ReadableProcessBuffer, ReadableProcessSlice, WriteableProcessSlice,
};
use crate::upcall::{PUpcall, Upcall, UpcallError, UpcallId};
use crate::{capabilities, debug, process, ErrorCode, ProcEntry, TIfCfg};

/// Tracks how many upcalls a grant instance supports automatically.
pub trait UpcallSize {
    /// The number of upcalls the grant supports.
    const COUNT: u8;
}

/// Specifies how many upcalls a grant instance supports automatically.
pub struct UpcallCount<const NUM: u8>;
impl<const NUM: u8> UpcallSize for UpcallCount<NUM> {
    const COUNT: u8 = NUM;
}

/// Tracks how many read-only allows a grant instance supports automatically.
pub trait AllowRoSize {
    /// The number of read-only allows the grant supports.
    const COUNT: u8;
}

/// Specifies how many read-only allows a grant instance supports automatically.
pub struct AllowRoCount<const NUM: u8>;
impl<const NUM: u8> AllowRoSize for AllowRoCount<NUM> {
    const COUNT: u8 = NUM;
}

/// Tracks how many read-write allows a grant instance supports automatically.
pub trait AllowRwSize {
    /// The number of read-write allows the grant supports.
    const COUNT: u8;
}

/// Specifies how many read-write allows a grant instance supports
/// automatically.
pub struct AllowRwCount<const NUM: u8>;
impl<const NUM: u8> AllowRwSize for AllowRwCount<NUM> {
    const COUNT: u8 = NUM;
}

/// Helper that calculated offsets within the kernel owned memory (i.e. the
/// non-T part of grant).
///
/// Example layout of full grant belonging to a single app and driver:
/// (If sizeof::<upcall> were 4 and align_of::<SavedUpcall> were 8.
///
/// ```text,ignore
/// 0x003FFC8  ┌────────────────────────────────────┐
///            │   T                                |
/// 0x003FFxx  ├  ───────────────────────── ┐       |
///            │   Padding (ensure T aligns)|       |
/// 0x003FF70  ├  ───────────────────────── |       |
///            │   SavedAllowRwN            | K     |
///            │   ...                      | e     | G
///            │   SavedAllowRw1            | r     | r
///            │   SavedAllowRw0            | n     | a
/// 0x003FF60  ├  ───────────────────────── | e     | n
///            │   SavedAllowRoN            | l     | t
///            │   ...                      |       |
///            │   SavedAllowRo1            | O     | M
///            │   SavedAllowRo0            | w     | e
/// 0x003FF50  ├  ───────────────────────── | n     | m
///            │   SavedUpcallN             | e     | o
///            │   ...                      | d     | r
///            │   SavedUpcall1             |       | y
///            │   SavedUpcall0             | D     |
/// 0x003FF40  ├  ───────────────────────── | a     |
///            │   Padding (align upcall)   | t     |
/// 0x003FF38  ├  ───────────────────────── | a     |
///            │   RefCell<>                |       |  (only if feature grant_refs)
/// 0x003FF28  ├  ───────────────────────── |       |
///            │   Counters (Cell<usize>)   |       |
/// 0x003FF20  └────────────────────────────────────┘
/// ```
///
/// The counters structure is composed as:
///
/// ```text,ignore
/// 0             1             2             3         bytes
/// |-------------|-------------|-------------|-------------|
/// | # Upcalls   | # RO Allows | # RW Allows | [unused]    |
/// |-------------|-------------|-------------|-------------|
/// ```
///
/// This type is created whenever a grant is entered, and is responsible for
/// ensuring that the grant is closed when it is no longer used. On `Drop`, we
/// leave the grant. This protects against calling `grant.enter()` without
/// calling the corresponding `grant.leave()`, perhaps due to accidentally using
/// the `?` operator.
struct EnteredGrantKernelManagedLayout<'a> {
    /// Leaving a grant is handled through the process implementation, so must
    /// keep a reference to the relevant process.
    process: &'a dyn Process,
    /// The grant number of the entered grant that we want to ensure we leave
    /// properly.
    grant_num: usize,

    /// The location of the counters structure for the grant.
    counters_ptr: *const Cell<usize>,
    /// Pointer to the array of saved upcalls.
    upcalls_array: *const SavedUpcall,
    /// Pointer to the array of saved read-only allows.
    allow_ro_array: *const SavedAllowRo,
    /// Pointer to the array of saved read-write allows.
    allow_rw_array: *const SavedAllowRw,
}

/// Represents the number of the upcall elements in the kernel owned section of
/// the grant.
#[derive(Copy, Clone)]
struct UpcallItems(u8);
/// Represents the number of the read-only allow elements in the kernel owned
/// section of the grant.
#[derive(Copy, Clone)]
struct AllowRoItems(u8);
/// Represents the number of the read-write allow elements in the kernel owned
/// section of the grant.
#[derive(Copy, Clone)]
struct AllowRwItems(u8);
/// Represents the size data (in bytes) T within the grant.
#[derive(Copy, Clone)]
struct GrantDataSize(usize);
/// Represents the alignment of data T within the grant.
#[derive(Copy, Clone)]
struct GrantDataAlign(usize);

/// The RefCell used in the Grant layout that contains the 'T'. The T is stored discontinuously, but
/// nominally belongs to the RefCell. The bool records if a Read-Only reference has been leaked.
type LayoutRefCell = RefCell<Cell<bool>>;

/// The fixed-size portion of the kernel managed layout
#[repr(C)]
struct KernelManagedLayoutFixed {
    counters: Cell<usize>,
    // Not RefCell<(bool,T)> in case T has to be very aligned, which would bloat the grant
    ref_cell: LayoutRefCell,
}

impl<'a> EnteredGrantKernelManagedLayout<'a> {
    /// Reads the specified pointer as the base of the kernel owned grant
    /// region.
    ///
    /// # Safety
    ///
    /// The incoming base pointer must be well aligned and already contain
    /// initialized data in the expected form. There must not be any other
    /// `EnteredGrantKernelManagedLayout` for the given `base_ptr` at the same
    /// time, otherwise multiple mutable references to the same upcall/allow
    /// slices could be created.
    #[inline]
    unsafe fn read_from_base(
        base_ptr: NonNull<u8>,
        process: &'a dyn Process,
        grant_num: usize,
    ) -> Self {
        // Safety: the requirements of as_ref are the same as this function.
        let fixed = base_ptr.cast::<KernelManagedLayoutFixed>().as_ref();
        let counters_ptr = base_ptr.as_ptr() as *const Cell<usize>;

        // Parse the counters field for each of the fields
        let [_, _, allow_ro_num, upcalls_num] = u32::to_be_bytes(fixed.counters.get() as u32);

        let upcalls_array = ((fixed as *const KernelManagedLayoutFixed).add(1) as *const u8)
            .add(Self::PADDING_BEFORE_ARRAY) as *const SavedUpcall;
        let allow_ro_array = upcalls_array.add(upcalls_num.into()) as *const SavedAllowRo;
        let allow_rw_array = allow_ro_array.add(allow_ro_num.into()) as *const SavedAllowRw;

        Self {
            process,
            grant_num,
            counters_ptr,
            upcalls_array,
            allow_ro_array,
            allow_rw_array,
        }
    }

    // Padding needed after the counts to ensure that array elements are aligned enough
    const PADDING_BEFORE_ARRAY: usize =
        (size_of::<KernelManagedLayoutFixed>()).wrapping_neg() % align_of::<SavedUpcall>();

    /// Creates a layout from the specified pointer and lengths of arrays and
    /// initializes the kernel owned portion of the layout.
    ///
    /// # Safety
    ///
    /// The incoming base pointer must be well aligned and reference enough
    /// memory to hold the entire kernel managed grant structure. There must
    /// not be any other `EnteredGrantKernelManagedLayout` for
    /// the given `base_ptr` at the same time, otherwise multiple mutable
    /// references to the same upcall/allow slices could be created.
    #[inline]
    unsafe fn initialize_from_counts(
        base_ptr: NonNull<u8>,
        upcalls_num_val: UpcallItems,
        allow_ro_num_val: AllowRoItems,
        allow_rw_num_val: AllowRwItems,
        process: &'a dyn Process,
        grant_num: usize,
    ) -> Self {
        debug_assert_eq!((base_ptr.as_ptr() as usize) % align_of::<SavedUpcall>(), 0);
        let kmlf_ref = base_ptr.cast::<KernelManagedLayoutFixed>().as_ref();
        let counters_ptr = core::ptr::addr_of!((*kmlf_ref).counters) as *mut Cell<usize>;

        // Create the counters usize value by correctly packing the various
        // counts into 8 bit fields.
        let counter: usize =
            u32::from_be_bytes([0, allow_rw_num_val.0, allow_ro_num_val.0, upcalls_num_val.0])
                as usize;

        let upcalls_array = ((base_ptr.as_ptr() as *const KernelManagedLayoutFixed).add(1)
            as *const u8)
            .add(Self::PADDING_BEFORE_ARRAY) as *const SavedUpcall;
        let allow_ro_array = upcalls_array.add(upcalls_num_val.0.into()) as *const SavedAllowRo;
        let allow_rw_array = allow_ro_array.add(allow_ro_num_val.0.into()) as *const SavedAllowRw;

        counters_ptr.write(Cell::new(counter.into()));
        write_default_array(upcalls_array as *mut u8, upcalls_num_val.0.into());
        write_default_array(allow_ro_array as *mut u8, allow_ro_num_val.0.into());
        write_default_array(allow_rw_array as *mut u8, allow_rw_num_val.0.into());

        Self {
            process,
            grant_num,
            counters_ptr,
            upcalls_array,
            allow_ro_array,
            allow_rw_array,
        }
    }

    /// Returns the entire grant size including the kernel own memory, padding,
    /// and data for T. Requires that grant_t_align be a power of 2, which is
    /// guaranteed from align_of rust calls.
    #[inline]
    fn grant_size(
        upcalls_num: UpcallItems,
        allow_ro_num: AllowRoItems,
        allow_rw_num: AllowRwItems,
        grant_t_size: GrantDataSize,
        grant_t_align: GrantDataAlign,
    ) -> usize {
        let kernel_managed_size = size_of::<KernelManagedLayoutFixed>()
            + Self::PADDING_BEFORE_ARRAY
            + upcalls_num.0 as usize * size_of::<SavedUpcall>() // Then the three arrays
            + allow_ro_num.0 as usize * size_of::<SavedAllowRo>()
            + allow_rw_num.0 as usize * size_of::<SavedAllowRw>();
        // We know that grant_t_align is a power of 2, so we can make a mask
        // that will save only the remainder bits.
        let grant_t_align_mask = grant_t_align.0 - 1;

        let total_size = kernel_managed_size + grant_t_size.0;

        // Align up
        (total_size + grant_t_align_mask) & !grant_t_align_mask
    }

    /// Returns the alignment of the entire grant region based on the alignment
    /// of data T.
    #[inline]
    fn grant_align(grant_t_align: GrantDataAlign) -> usize {
        // We need the highest alignment of all objects in the grant to ensure our padding
        // calculations work for any alignment of T.
        // We put the three variable length arrays in alignment order.
        assert!(
            align_of::<SavedUpcall>() >= align_of::<SavedAllowRo>()
                && align_of::<SavedAllowRo>() >= align_of::<SavedAllowRw>()
        );
        cmp::max(
            cmp::max(
                align_of::<KernelManagedLayoutFixed>(),
                align_of::<SavedUpcall>(),
            ),
            grant_t_align.0,
        )
    }

    /// Returns the grant data pointer given the base pointer
    ///
    /// # Safety
    ///
    /// The caller must ensure that the specified base pointer is aligned to at
    /// least the alignment of T and points to a grant that is of size
    /// grant_size bytes.
    #[inline]
    unsafe fn get_grant_data_t(
        base_ptr: NonNull<u8>,
        grant_size: usize,
        grant_t_size: GrantDataSize,
    ) -> NonNull<u8> {
        // The location of the grant data T is the last element in the entire
        // grant region. Caller must verify that memory is accessible and well
        // aligned to T.
        let grant_t_size_usize: usize = grant_t_size.0;
        NonNull::new_unchecked(base_ptr.as_ptr().add(grant_size - grant_t_size_usize))
    }

    /// Returns a pointer to the RefCell for the grant data given the base pointer.
    #[inline]
    unsafe fn get_grant_data_t_ref(base_ptr: NonNull<u8>) -> NonNull<LayoutRefCell> {
        NonNull::new_unchecked(core::ptr::addr_of_mut!(
            (*(base_ptr.as_ptr() as *mut KernelManagedLayoutFixed)).ref_cell
        ))
    }

    /// Read an 8 bit value from the counter field offset by the specified
    /// number of bits. This is a helper function for reading the counter field.
    fn get_counter_offset(&self, offset_bits: usize) -> usize {
        // # Safety
        //
        // Creating a `EnteredGrantKernelManagedLayout` object requires that the
        // pointers are well aligned and point to valid memory.
        let counters_val = unsafe { self.counters_ptr.read() };
        (counters_val.get() >> offset_bits) & 0xFF
    }

    /// Return the number of upcalls stored by the core kernel for this grant.
    fn get_upcalls_number(&self) -> usize {
        self.get_counter_offset(0)
    }

    /// Return the number of read-only allow buffers stored by the core kernel
    /// for this grant.
    fn get_allow_ro_number(&self) -> usize {
        self.get_counter_offset(8)
    }

    /// Return the number of read-write allow buffers stored by the core kernel
    /// for this grant.
    fn get_allow_rw_number(&self) -> usize {
        self.get_counter_offset(16)
    }

    /// Return immutable access to the slice of stored upcalls for this grant.
    /// Use .set method for storing a new upcall.
    fn get_upcalls_slice(&self) -> &[SavedUpcall] {
        // # Safety
        //
        // Creating a `EnteredGrantKernelManagedLayout` object ensures that the
        // pointer to the upcall array is valid.
        unsafe {
            slice::from_raw_parts(
                self.upcalls_array as *const SavedUpcall,
                self.get_upcalls_number(),
            )
        }
    }

    /// Return immutable access to the slice of stored read-only allow buffers for
    /// this grant. Use .set method for storing a new read-only allow.
    fn get_allow_ro_slice(&self) -> &[SavedAllowRo] {
        // # Safety
        //
        // Creating a `EnteredGrantKernelManagedLayout` object ensures that the
        // pointer to the RO allow array is valid.
        unsafe {
            slice::from_raw_parts(
                self.allow_ro_array as *const SavedAllowRo,
                self.get_allow_ro_number(),
            )
        }
    }

    /// Return immutable access to the slice of stored read-write allow buffers
    /// for this grant. Use .set method for storing a new read-write allow.
    fn get_allow_rw_slice(&self) -> &[SavedAllowRw] {
        // # Safety
        //
        // Creating a `EnteredGrantKernelManagedLayout` object ensures that the
        // pointer to the RW allow array is valid.
        unsafe {
            slice::from_raw_parts(
                self.allow_rw_array as *const SavedAllowRw,
                self.get_allow_rw_number(),
            )
        }
    }

    /// Return slices to the kernel managed upcalls and allow buffers. This
    /// permits using upcalls and allow buffers when a capsule is accessing a
    /// grant.
    fn get_resource_slices(&self) -> (&[SavedUpcall], &[SavedAllowRo], &[SavedAllowRw]) {
        // # Safety
        //
        // Creating a `EnteredGrantKernelManagedLayout` object ensures that the
        // pointer to the upcall array is valid.
        let upcall_slice =
            unsafe { slice::from_raw_parts(self.upcalls_array, self.get_upcalls_number()) };

        // # Safety
        //
        // Creating a `EnteredGrantKernelManagedLayout` object ensures that the
        // pointer to the RO allow array is valid.
        let allow_ro_slice =
            unsafe { slice::from_raw_parts(self.allow_ro_array, self.get_allow_ro_number()) };

        // # Safety
        //
        // Creating a `KernelManagedLayout` object ensures that the pointer to
        // the RW allow array is valid.
        let allow_rw_slice =
            unsafe { slice::from_raw_parts(self.allow_rw_array, self.get_allow_rw_number()) };

        (upcall_slice, allow_ro_slice, allow_rw_slice)
    }
}

/// This GrantData object provides access to the memory allocated for a grant
/// for a specific process.
///
/// The GrantData type is templated on T, the actual type of the object in the
/// grant. GrantData holds a mutable reference to the type, allowing users
/// access to the object in process memory.
///
/// Capsules gain access to a GrantData object by calling `Grant::enter()`.
pub struct GrantData<'a, T: 'a + ?Sized> {
    /// The mutable reference to the actual object type stored in the grant,
    data: &'a mut T,
}

/// New grant data wrapper. Can provide one of three interfaces:
/// 1) The legacy interface. Can be borrowed inside a closure to provide a `GrantData<T>` which is
/// short lived smart pointer to a T.
/// 2) The new interface. Provides a `PRef<T>`. `PRef<T>` can be long lived, and can be converted back
/// and forth with a `LivePRef<T>` (also a smart pointer to a T). Converting checks that the process
/// is still live.
/// 3) A reference counted interface for DMA. Provides a `Ref<T>` or `RefMut<T>`.
/// Note taking out a `Pref<T>` will _permanently_ disallow legacy enter and the reference counted
/// RefMut interface.

pub struct NewGrantData<'a, T: 'a> {
    ref_cell: &'a LayoutRefCell,
    the_t: NonNull<T>,
    proc_entry: &'static ProcEntry,
}

impl<'a, T: 'a> NewGrantData<'a, T> {
    #[inline]
    fn new(ref_cell: &'a LayoutRefCell, the_t: NonNull<T>, proc_entry: &'static ProcEntry) -> Self {
        Self {
            ref_cell,
            the_t,
            proc_entry,
        }
    }

    /// Get a RefMut for the grant data. Taking this and not dropping it will mean all future
    /// calls will return None.
    /// It will also block the grant from being freed if the process dies.
    /// Only use this if you _really_ need the reference to outlive a single syscall.
    /// If you don't, prefer getting a Pref<T>.
    #[inline]
    fn priv_try_get_ref_mut<'b>(&self) -> Option<RefMut<'b, T>>
    where
        T: 'b,
    {
        match self.ref_cell.try_borrow_mut() {
            Ok(borrowed) => {
                let mut raw_ptr = self.the_t;
                Some({
                    // SAFETY: The unit in the refcell was always meant to point to this data
                    let value_short = RefMut::map(borrowed, |_| unsafe { raw_ptr.as_mut() });
                    // SAFETY: T lives as long as 'b because of bound on function.
                    // We ensure elsewhere that the RefCell will not be dropped / moved while any
                    // of these references still exist.
                    unsafe { core::mem::transmute::<RefMut<'a, T>, RefMut<'b, T>>(value_short) }
                })
            }
            Err(_) => None,
        }
    }

    /// See try_get_ref_mut. This will allow multiple Refs to exist.
    #[inline]
    fn priv_try_get_ref<'b>(&self) -> Option<Ref<'b, T>>
    where
        T: 'b,
    {
        match self.ref_cell.try_borrow() {
            Ok(borrowed) => {
                let raw_ptr = self.the_t;
                Some({
                    // SAFETY: The refcell was always meant to include this data.
                    let value_short = Ref::map(borrowed, |_| unsafe { raw_ptr.as_ref() });
                    // SAFETY: T lives as long as 'b because of bound on function.
                    // We ensure elsewhere that the RefCell will not be dropped / moved while any
                    // of these references still exist.
                    unsafe { core::mem::transmute::<Ref<'a, T>, Ref<'b, T>>(value_short) }
                })
            }
            Err(_) => None,
        }
    }

    /// Get a short-lived reference to the data for the lifetime of a closure. Because the reference
    /// cannot leak the closure, it may be difficult for functions of the reference to be stored.
    /// Prefer get_pref() if you want to pass data into other capsules / HALs.
    #[inline]
    pub fn legacy_enter<F, R>(
        &self,
        fun: F,
        panic_on_reenter: bool,
        kern_data: &GrantKernelData,
        allocator: &mut GrantRegionAllocator,
    ) -> Option<R>
    where
        F: FnOnce(&mut GrantData<T>, &GrantKernelData, &mut GrantRegionAllocator) -> R,
    {
        match self.priv_try_get_ref_mut() {
            Some(mut re) => Some(fun(
                &mut GrantData::new(re.deref_mut()),
                kern_data,
                allocator,
            )),
            None => {
                // If we get an error it is because the grant is already
                // entered. `process.enter_grant()` can fail for several
                // reasons, but only the double enter case can happen once a
                // grant has been applied. The other errors would be detected
                // earlier (i.e. before the grant can be applied).

                // If `panic_on_reenter` is false, we skip this error and do
                // nothing with this grant.
                if !panic_on_reenter {
                    return None;
                }

                // If `enter_grant` fails, we panic!() to notify the developer
                // that they tried to enter the same grant twice which is
                // prohibited because it would result in two mutable references
                // existing for the same memory. This preserves type correctness
                // (but does crash the system).
                //
                // ## Explanation and Rationale
                //
                // This panic represents a tradeoff. While it is undesirable to
                // have the potential for a runtime crash in this grant region
                // code, it balances usability with type correctness. The
                // challenge is that calling `self.apps.iter()` is a common
                // pattern in capsules to access the grant region of every app
                // that is using the capsule, and sometimes it is intuitive to
                // call that inside of a `self.apps.enter(app_id, |app| {...})`
                // closure. However, `.enter()` means that app's grant region is
                // entered, and then a naive `.iter()` would re-enter the grant
                // region and cause undefined behavior. We considered different
                // options to resolve this.
                //
                // 1. Have `.iter()` only iterate over grant regions which are
                //    not entered. This avoids the bug, but could lead to
                //    unexpected behavior, as `self.apps.iter()` will do
                //    different things depending on where in a capsule it is
                //    called.
                // 2. Have the compiler detect when `.iter()` is called when a
                //    grant region has already been entered. We don't know of a
                //    viable way to implement this.
                // 3. Panic if `.iter()` is called when a grant is already
                //    entered.
                //
                // We decided on option 3 because it balances minimizing
                // surprises (`self.apps.iter()` will always iterate all grants)
                // while also protecting against the bug. We expect that any
                // code that attempts to call `self.apps.iter()` after calling
                // `.enter()` will immediately encounter this `panic!()` and
                // have to be refactored before any tests will be successful.
                // Therefore, this `panic!()` should only occur at
                // development/testing time.
                //
                // ## How to fix this error
                //
                // If you are seeing this panic, you need to refactor your
                // capsule to not call `.iter()` or `.each()` from inside a
                // `.enter()` closure. That is, you need to close the grant
                // region you are currently in before trying to iterate over all
                // grant regions.
                panic!("Attempted to re-enter a grant region.");
            }
        }
    }

    /// Get a process-lifetime bound reference to grant data.
    /// LivePRef can be converted back to PRef type for storage which ascribes
    /// to 'static. To convert back, use `TryInto<LivePRef<T>>`.
    #[inline]
    pub fn get_pref(&self) -> Option<LivePRef<'a, T>> {
        match self.ref_cell.try_borrow() {
            Ok(r) => {
                if !r.get() {
                    // PRef leaks a count to block concurrent use by the other interfaces.
                    // Preferred over PRef containing a Ref as that would add extra code
                    // generation to the common case of only Pref<T> being in use.
                    // We only do this once so that repeated use of get_pref does not overflow the
                    // counter and on terminate can magically resurrect this reference.
                    r.set(true);
                    core::mem::forget(r);
                }
                // Safety: leaking a reference blocks any exclusive references being created
                // NewGrantData cannot outlive a process so the process is valid at this point.
                unsafe { Some(LivePRef::new(self.the_t, self.proc_entry)) }
            }
            Err(_) => None,
        }
    }

    /// Public version of priv_try_get_ref_mut
    #[inline]
    pub fn try_get_ref_mut<'b>(
        &self,
        _cap: &'static dyn capabilities::HoldGrantReferencesCapability,
    ) -> Option<RefMut<'b, T>>
    where
        T: 'b + Sized,
    {
        self.priv_try_get_ref_mut()
    }

    /// Public version of priv_try_get_ref
    #[inline]
    pub fn try_get_ref<'b>(
        &self,
        _cap: &'static dyn capabilities::HoldGrantReferencesCapability,
    ) -> Option<Ref<'b, T>>
    where
        T: 'b + Sized,
    {
        self.priv_try_get_ref()
    }
}

impl<'a, T: 'a + ?Sized> GrantData<'a, T> {
    /// Create a `GrantData` object to provide access to the actual object
    /// allocated for a process.
    ///
    /// Only one can GrantData per underlying object can be created at a time.
    /// Otherwise, there would be multiple mutable references to the same object
    /// which is undefined behavior.
    #[inline]
    fn new(data: &'a mut T) -> GrantData<'a, T> {
        GrantData { data }
    }
}

/// This can now panic for the reference counted version. Would be nice to offer a better
/// interface.
/// Maybe users of Grant<> should select which style they prefer, and this should not be offered for
/// the reference counted versions.
impl<'a, T: 'a + ?Sized> Deref for GrantData<'a, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        self.data
    }
}

impl<'a, T: 'a + ?Sized> DerefMut for GrantData<'a, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        self.data
    }
}

/// This GrantKernelData object provides a handle to access upcalls and process
/// buffers stored on behalf of a particular grant/driver.
///
/// Capsules gain access to a GrantKernelData object by calling
/// `Grant::enter()`. From there, they can schedule upcalls or access process
/// buffers.
///
/// It is expected that this type will only exist as a short-lived stack
/// allocation, so its size is not a significant concern.
pub struct GrantKernelData<'a> {
    /// A reference to the actual upcall slice stored in the grant.
    upcalls: &'a [SavedUpcall],

    /// A reference to the actual read only allow slice stored in the grant.
    allow_ro: &'a [SavedAllowRo],

    /// A reference to the actual read write allow slice stored in the grant.
    allow_rw: &'a [SavedAllowRw],

    /// We need to keep track of the driver number so we can properly identify
    /// the Upcall that is called. We need to keep track of its source so we can
    /// remove it if the Upcall is unsubscribed.
    driver_num: usize,

    /// A reference to the process that these upcalls are for. This is used for
    /// actually scheduling the upcalls.
    process: &'a dyn Process,
}

impl<'a> GrantKernelData<'a> {
    /// Create a `GrantKernelData` object to provide a handle for capsules to
    /// call Upcalls.
    fn new(
        upcalls: &'a [SavedUpcall],
        allow_ro: &'a [SavedAllowRo],
        allow_rw: &'a [SavedAllowRw],
        driver_num: usize,
        process: &'a dyn Process,
    ) -> GrantKernelData<'a> {
        Self {
            upcalls,
            allow_ro,
            allow_rw,
            driver_num,
            process,
        }
    }

    /// Get the reference to the process that this grant data is for. This being available avoids
    /// boilerplate of looking up the process again after entering a grant. Should be pub(crate)
    /// otherwise the process management cap could be sidestepped.
    /// I would like to see more of that interface have caps added, and then make this always
    /// available. Or at least give a proxy object.
    pub(crate) fn get_process(&self) -> &'a dyn Process {
        self.process
    }

    /// Schedule the specified upcall for the process with r0, r1, r2 as
    /// provided values.
    ///
    /// Capsules call this function to schedule upcalls, and upcalls are
    /// identified by the `subscribe_num`, which must match the subscribe number
    /// used when the upcall was originally subscribed by a process.
    /// `subscribe_num`s are indexed starting at zero.
    pub fn schedule_upcall(
        &self,
        subscribe_num: usize,
        r: (usize, usize, usize),
    ) -> Result<(), UpcallError> {
        // Implement `self.upcalls[subscribe_num]` without a chance of a panic.
        self.upcalls.get(subscribe_num).map_or(
            Err(UpcallError::InvalidSubscribeNum),
            |saved_upcall| {
                // We can create an `Upcall` object based on what is stored in
                // the process grant and use that to add the upcall to the
                // pending array for the process.
                let mut upcall = Upcall::new(
                    self.process.processid(),
                    UpcallId {
                        subscribe_num,
                        driver_num: self.driver_num,
                    },
                    saved_upcall.appdata.get(),
                    saved_upcall.fn_ptr.get(),
                );
                upcall.schedule(self.process, r.0, r.1, r.2)
            },
        )
    }

    pub fn could_schedule_upcall(&self, subscribe_num: usize) -> Result<(), UpcallError> {
        self.upcalls.get(subscribe_num).map_or(
            Err(UpcallError::InvalidSubscribeNum),
            |saved_upcall| {
                saved_upcall.fn_ptr.get().map_or(Ok(()), |_| {
                    self.process.could_enqueue_task().map_err(|er| match er {
                        ErrorCode::NOMEM => UpcallError::QueueFull,
                        _ => UpcallError::KernelError,
                    })
                })
            },
        )
    }

    pub fn get_upcall(&self, subscribe_num: usize) -> PUpcall {
        let (tracker, fptr, data) = self.upcalls.get(subscribe_num).map_or(
            (
                DualTracker::global_dead(),
                Default::default(),
                Default::default(),
            ),
            |saved_upcall| {
                let id = self.process.processid();
                (
                    DualTracker::new(
                        id.kernel.get_live_tracker_for(id),
                        ALiveTracker::new(&saved_upcall.live),
                    ),
                    saved_upcall.fn_ptr.get(),
                    saved_upcall.appdata.get(),
                )
            },
        );
        PUpcall::new(
            tracker,
            data,
            fptr,
            UpcallId {
                driver_num: self.driver_num,
                subscribe_num,
            },
        )
    }

    pub fn has_nonnull_upcall(&self, subscribe_num: usize) -> bool {
        self.upcalls
            .get(subscribe_num)
            .map_or(false, |saved_upcall| {
                saved_upcall.fn_ptr.get().map_or(false, |_| true)
            })
    }

    /// Common logic between get_readonly_processbuffer, get_readwrite_processbuffer,
    /// and the ARef versions.
    fn get_helper(
        &self,
        allow_num: usize,
        ro: bool,
    ) -> Result<(*const [u8], &Cell<ATrackerInt>), Error> {
        let saved_allow = if ro { &self.allow_ro } else { &self.allow_rw }
            .get(allow_num)
            .ok_or(crate::process::Error::AddressOutOfBounds)?;

        let ptr = saved_allow.value.0.map_ref(
            |true_ref| unsafe {
                // Safety: we never get_mut on this refcell.
                *true_ref.as_ptr()
            },
            |false_ref| false_ref.get(),
        );

        let tracker = &saved_allow.live;

        Ok((ptr, tracker))
    }

    fn get_rc_helper(
        &self,
        allow_num: usize,
        ro: bool,
    ) -> Result<Ref<'static, *const [u8]>, crate::process::Error> {
        if !CONFIG.counted_grant_refs {
            return Err(Error::KernelError);
        }

        let saved_allow = if ro { &self.allow_ro } else { &self.allow_rw }
            .get(allow_num)
            .ok_or(crate::process::Error::AddressOutOfBounds)?;

        // # Safety:
        // For as long as the reference counter is non-zero, the RefCell will not be changed
        // due to the logic in allow_ro and ... (TODO: don't allow process free while counts).
        // So, we can transmute this reference to have static lifetime as the only danger
        // of that would it be outliving its Refcell, which we will keep around until
        // the count is zero.
        // We could have used Rc<T> to have not needed the lifetime at all,
        // but Rc<T> does not expose its cell like Ref does with RefCell.

        unsafe {
            let as_static: Option<Ref<'static, *const [u8]>> =
                core::mem::transmute(saved_allow.value.0.get_true_ref().try_borrow());
            as_static.ok_or(crate::process::Error::AlreadyInUse)
        }
    }

    /// Returns a lifetime limited reference to the requested
    /// `ReadOnlyProcessBuffer`.
    ///
    /// The `ReadOnlyProcessBuffer` is only valid for as long as this object is
    /// valid, i.e. the lifetime of the app enter closure.
    ///
    /// If the specified allow number is invalid, then a AddressOutOfBounds will
    /// be returned. This returns a process::Error to allow for easy chaining of
    /// this function with the ReadOnlyProcessBuffer::enter function with
    /// `and_then`.
    pub fn get_readonly_processbuffer(
        &self,
        allow_ro_num: usize,
    ) -> Result<ReadOnlyProcessBufferRef, crate::process::Error> {
        let (ptr, _) = self.get_helper(allow_ro_num, true)?;

        // # Safety
        //
        // This is the saved process buffer data has been validated to
        // be wholly contained within this process before it was stored.
        // The lifetime of the ReadOnlyProcessBuffer is bound to the
        // lifetime of self, which correctly limits dereferencing this
        // saved pointer to only when it is valid.
        unsafe {
            Ok(ReadOnlyProcessBufferRef::new(
                ptr.as_ptr(),
                ptr.len(),
                self.process.processid(),
            ))
        }
    }

    /// Helper to reduce boilerplate for get + and_then + enter
    pub fn enter_readonly_processbuffer<F, R>(
        &self,
        allow_ro_num: usize,
        fun: F,
    ) -> Result<R, process::Error>
    where
        F: FnOnce(&ReadableProcessSlice) -> R,
    {
        self.get_readonly_processbuffer(allow_ro_num)
            .and_then(|buf| buf.enter(fun))
    }

    /// Get a reference counted reference to the requested `ReadOnlyProcessBuffer`
    /// This reference is a valid for longer, but no new buffer can be allowed while references
    /// Still exist. This may cause a loss in stability.
    /// To encourage use of the other interface, this one requires a capability.
    pub fn get_readonly_processbuffer_rc(
        &self,
        allow_ro_num: usize,
        _cap: &dyn capabilities::HoldAllowReferencesCapability,
    ) -> Result<Ref<'static, ReadableProcessSlice>, crate::process::Error> {
        let as_static = self.get_rc_helper(allow_ro_num, true)?;

        Ok(Ref::map(as_static, |slice| {
            // We can also avoid the extra indirection (and any possibly problematic
            // changing of the RefCell) by following the pointer through the RefCell and
            // converting the slice to something more typesafe.
            // This has the benefit of allowing re-use of the slot, and stopping the pointer from
            // changing from underneath us.
            let slice = *slice;
            unsafe { raw_processbuf_to_roprocessslice::<'static>(slice.as_ptr(), slice.len()) }
        }))
    }

    /// Returns a lifetime limited reference to the requested
    /// `ReadWriteProcessBuffer`.
    ///
    /// The ReadWriteProcessBuffer is only value for as long as this object is
    /// valid, i.e. the lifetime of the app enter closure.
    ///
    /// If the specified allow number is invalid, then a AddressOutOfBounds will
    /// be return. This returns a process::Error to allow for easy chaining of
    /// this function with the `ReadWriteProcessBuffer::enter()` function with
    /// `and_then`.
    pub fn get_readwrite_processbuffer(
        &self,
        allow_rw_num: usize,
    ) -> Result<ReadWriteProcessBufferRef, crate::process::Error> {
        let (ptr, _) = self.get_helper(allow_rw_num, false)?;

        // # Safety
        //
        // This is the saved process buffer data has been validated to
        // be wholly contained within this process before it was stored.
        // The lifetime of the ReadWriteProcessBuffer is bound to the
        // lifetime of self, which correctly limits dereferencing this
        // saved pointer to only when it is valid.
        unsafe {
            Ok(ReadWriteProcessBufferRef::new(
                (ptr as *mut [u8]).as_mut_ptr(),
                ptr.len(),
                self.process.processid(),
            ))
        }
    }

    /// Get a reference counted reference to the requested `ReadWriteProcessBuffer`
    /// This reference is a valid for longer, but no buffer can be allowed while references
    /// Still exist. This may cause a loss in stability.
    /// Note, this is only a Ref, not RefMut, because WritetableProcessSlice might overlap with
    /// other allowed buffers. The interior mutability of the type allows for writing.
    pub fn get_readwrite_processbuffer_rc(
        &self,
        allow_rw_num: usize,
        _cap: &dyn capabilities::HoldAllowReferencesCapability,
    ) -> Result<Ref<'static, WriteableProcessSlice>, crate::process::Error> {
        let as_static = self.get_rc_helper(allow_rw_num, false)?;

        Ok(Ref::map(as_static, |slice| {
            // We can also avoid the extra indirection (and any possibly problematic
            // changing of the RefCell) by following the pointer through the RefCell and
            // converting the slice to something more typesafe.
            // This has the benefit of allowing re-use of the slot, and stopping the pointer from
            // changing from underneath us.
            let slice = *slice;
            unsafe {
                raw_processbuf_to_rwprocessslice::<'static>(slice.as_ptr() as *mut u8, slice.len())
            }
        }))
    }

    /// Get a LiveARef for an read-only allowed buffer. It is always valid, but has limited
    /// lifetime. Convert into ARef which ascribes to static to store.
    pub fn get_readonly_aref(
        &self,
        allow_ro_num: usize,
    ) -> Result<LiveARef<ReadableProcessSlice>, ErrorCode> {
        let (ptr, tracker) = self.get_helper(allow_ro_num, true)?;
        let buf = unsafe { raw_processbuf_to_roprocessslice(ptr.as_ptr(), ptr.len()) };
        let id = self.process.processid();
        unsafe {
            // Safety: the existence of this object means the process is currently live.
            Ok(LiveARef::new(
                buf.into(),
                id.kernel.get_live_tracker_for(id),
                tracker,
            ))
        }
    }

    /// Get a LiveARef for an read/write allowed buffer. It is always valid, but has limited
    /// lifetime. Convert into ARef which ascribes to static to store.
    pub fn get_readwrite_aref(
        &self,
        allow_rw_num: usize,
    ) -> Result<LiveARef<WriteableProcessSlice>, ErrorCode> {
        let (ptr, tracker) = self.get_helper(allow_rw_num, false)?;
        let buf = unsafe { raw_processbuf_to_rwprocessslice(ptr.as_ptr() as *mut u8, ptr.len()) };
        let id = self.process.processid();
        unsafe {
            // Safety: the existence of this object means the process is currently live.
            Ok(LiveARef::new(
                buf.into(),
                id.kernel.get_live_tracker_for(id),
                tracker,
            ))
        }
    }

    pub fn get_extra_syscall_arg(&self, ndx: usize) -> Option<usize> {
        self.get_process().get_extra_syscall_arg(ndx)
    }
}

/// A minimal representation of an upcall, used for storing an upcall in a
/// process' grant table without wasting memory duplicating information such as
/// process ID.
#[repr(C)]
#[derive(Default)]
struct SavedUpcall {
    appdata: Cell<crate::upcall::AppdataType>,
    fn_ptr: Cell<crate::upcall::FnPtrType>,
    /// It is up to applications when to rotate these. The kernel promises to stop using the ref
    /// upon request.
    /// For libtock-rs, this is controlled by `scope::share`.
    /// At the END of any `scope::share` any buffers shared within that block are un-allowed by
    /// rotating the counter. Entering a block does not rotate the counter, so a nested share
    /// will not immediately unshare previous buffers.
    live: Cell<ATrackerInt>,
}

/// A wrapper of a raw slice, possibly with a ref count if enabled
/// It doesn't really matter this is *const or *mut for our use cases
type AllowSliceTIf = TIfCfg!(counted_grant_refs, RefCell<*const [u8]>, Cell<*const [u8]>);
/// Wrapping again to implement Default
struct AllowSliceInner(AllowSliceTIf);

impl AllowSliceInner {
    fn new(value: *const [u8]) -> Self {
        if CONFIG.counted_grant_refs {
            AllowSliceInner(AllowSliceTIf::new_true(RefCell::new(value)))
        } else {
            AllowSliceInner(AllowSliceTIf::new_false(Cell::new(value)))
        }
    }

    /// Try replace the slice pointer with another.
    /// On failure, returns the input and false.
    /// On success, returns the value and true.
    /// If unallow_previous is true, then it will give back the last allowed value, otherwise,
    /// NULL is returned.
    fn try_replace(&self, value: *const [u8], unallow_previous: bool) -> (*const [u8], bool) {
        if unallow_previous {
            if CONFIG.counted_grant_refs {
                match self.0.get_true_ref().try_borrow_mut() {
                    Ok(mut ref_mut) => (core::mem::replace(ref_mut.deref_mut(), value), true),
                    Err(_) => (value, false),
                }
            } else {
                (self.0.get_false_ref().replace(value), true)
            }
        } else {
            // If we are not unallowing the previous buffers, then it does not matter if there
            // are any reference counts.
            if CONFIG.counted_grant_refs {
                unsafe {
                    *self.0.get_true_ref().as_ptr() = value;
                }
            } else {
                self.0.get_false_ref().set(value);
            }
            (core::ptr::slice_from_raw_parts(0 as *const u8, 0), true)
        }
    }

    fn new_null() -> Self {
        Self::new(core::ptr::slice_from_raw_parts(core::ptr::null(), 0))
    }
}

impl Default for AllowSliceInner {
    fn default() -> Self {
        Self::new_null()
    }
}

/// A minimal representation of a read-only allow from app, used for storing a
/// read-only allow in a process' kernel managed grant space without wasting
/// memory duplicating information such as process ID.
#[repr(C)]
#[derive(Default)]
struct SavedAllowRo {
    value: AllowSliceInner,
    /// It is up to applications when to rotate these. For rust, a change corresponds to the END
    /// of any lifetime of scope::share
    live: Cell<ATrackerInt>,
}

/// A minimal representation of a read-write allow from app, used for storing a
/// read-write allow in a process' kernel managed grant space without wasting
/// memory duplicating information such as process ID.
type SavedAllowRw = SavedAllowRo;

/// Write the default value of T to every element of the array.
///
/// # Safety
///
/// The pointer must be well aligned and point to allocated memory that is
/// writable for `size_of::<T> * num` bytes. No Rust references may exist to
/// memory in the address range spanned by `base..base+num` at the time this
/// function is called. The memory does not need to be initialized yet. If it
/// already does contain initialized memory, then those contents will be
/// overwritten without being `Drop`ed first.
#[inline]
unsafe fn write_default_array<T: Default>(base: *mut T, num: usize) {
    for i in 0..num {
        base.add(i).write(T::default());
    }
}

/// Enters the grant for the specified process. Caller must hold on to the grant
/// lifetime guard while they accessing the memory in the layout (second
/// element).
fn enter_grant_kernel_managed(
    process: &dyn Process,
    driver_num: usize,
) -> Result<EnteredGrantKernelManagedLayout, ErrorCode> {
    let grant_num = process.lookup_grant_from_driver_num(driver_num)?;
    let mem = process.get_grant_mem(grant_num)?;

    // # Safety
    //
    // We know that this pointer is well aligned and initialized with meaningful
    // data when the grant region was allocated.
    match mem {
        None => Err(ErrorCode::NOMEM),
        Some(mem) => {
            Ok(unsafe { EnteredGrantKernelManagedLayout::read_from_base(mem, process, grant_num) })
        }
    }
}

/// Subscribe to an upcall by saving the upcall in the grant region for the
/// process and returning the existing upcall for the same UpcallId.
pub(crate) fn subscribe(
    process: &dyn Process,
    upcall: Upcall,
) -> Result<Upcall, (Upcall, ErrorCode)> {
    // Enter grant and keep it open until _grant_open goes out of scope.
    let layout = match enter_grant_kernel_managed(process, upcall.upcall_id.driver_num) {
        Ok(val) => val,
        Err(e) => return Err((upcall, e)),
    };

    // Create the saved upcalls slice from the grant memory.
    //
    // # Safety
    //
    // This is safe because of how the grant was initially allocated and that
    // because we were able to enter the grant the grant region must be valid
    // and initialized. We are also holding the grant open until `_grant_open`
    // goes out of scope.
    let saved_upcalls_slice = layout.get_upcalls_slice();

    // Index into the saved upcall slice to get the old upcall. Use .get in case
    // userspace passed us a bad subscribe number.
    match saved_upcalls_slice.get(upcall.upcall_id.subscribe_num) {
        Some(saved_upcall) => {
            // Create an `Upcall` object with the old saved upcall.
            let old_upcall = Upcall::new(
                process.processid(),
                upcall.upcall_id,
                saved_upcall.appdata.get(),
                saved_upcall.fn_ptr.get(),
            );

            // Overwrite the saved upcall with the new upcall.
            saved_upcall.appdata.set(upcall.appdata);
            saved_upcall.fn_ptr.set(upcall.fn_ptr);

            // Success!
            Ok(old_upcall)
        }
        None => Err((upcall, ErrorCode::NOSUPPORT)),
    }
}

/// Revoke all allow-ed buffers that match a predicate P.
/// Safety: no LiveARef or LivePRef may exist to anything filtered out, nor may any grants be
/// entered via the legacy mechanism.
pub unsafe fn revoke_allows<P: FnMut(*const [u8]) -> bool>(
    kernel: &Kernel,
    process: &dyn Process,
    mut p: P,
) -> Result<(), ErrorCode> {
    let max = kernel.get_grant_count_and_finalize();

    for driver_num in 0..max {
        let Ok(layout) = enter_grant_kernel_managed(process, driver_num) else {
            continue;
        };

        for vector in [layout.get_allow_ro_slice(), layout.get_allow_rw_slice()] {
            for allow in vector {
                let range = if CONFIG.counted_grant_refs {
                    // This error happens if this function is called inside of a legacy enter,
                    // which breaks its safe contract.
                    *allow
                        .value
                        .0
                        .get_true_ref()
                        .try_borrow()
                        .or(Err(ErrorCode::BUSY))?
                } else {
                    allow.value.0.get_false_ref().get()
                };
                if p(range) {
                    let (_, success) = allow
                        .value
                        .try_replace(core::ptr::slice_from_raw_parts(core::ptr::null(), 0), true);
                    // Attempt to revoke a reference counted allow
                    if !success {
                        return Err(ErrorCode::BUSY);
                    } else {
                        debug!("We got rid of: {}", range.as_ptr() as usize);
                    }
                }
            }
        }

        // Note: upcalls will be revoked because they are stored as CHERI capabilities
    }

    Ok(())
}

pub(crate) fn try_free_grant(process: &dyn Process) -> Result<(), ErrorCode> {
    // TODO: open as each driver
    let driver_num: usize = 0;
    // Enter grant and keep it open until `_grant_open` goes out of scope.
    let layout = match enter_grant_kernel_managed(process, driver_num) {
        Ok(val) => val,
        Err(e) => match e {
            // Some of these mean the grant is already free
            ErrorCode::NOMEM => return Ok(()),
            // Others, propagate the error
            _ => return Err(e),
        },
    };

    // Now try take each of the allowed buffers mutably. If any fail, we fail.

    let _saved_allow_ro_slice = layout.get_allow_ro_slice();
    let _saved_allow_rw_slice = layout.get_allow_rw_slice();

    // TODO actually loop through the slices
    // TODO also check the T in the grant has no references
    // TODO also check custom grants have no references
    todo!();
}

/// Stores the process buffer in the kernel managed grant
/// Safety: ptr, len has been validated and has actually been allowed to us by the process.
/// If unallow_previous is true then all previously allowed buffers (to this slot) will no longer
/// be used by the kernel.
/// Currently, we use whether a Null ptr is passed as whether this is intended by the user, as this
/// matches the patterns used in userspace.
/// However, it does not quite match the original tock interface and so might break some downsteam
/// code. We could also have a separate syscall that explicitly says this is false.
pub(crate) unsafe fn allow_helper(
    process: &dyn Process,
    driver_num: usize,
    allow_num: usize,
    ptr: *const u8,
    len: usize,
    read_only: bool,
    unallow_previous: bool,
) -> (*const u8, usize, Result<(), ErrorCode>) {
    // Enter grant
    let layout = match enter_grant_kernel_managed(process, driver_num) {
        Ok(layout) => layout,
        Err(e) => return (ptr, len, Err(e)),
    };

    let saved_slice = if read_only {
        layout.get_allow_ro_slice()
    } else {
        layout.get_allow_rw_slice()
    };

    // Index into the saved slice to get the old value. Use .get in case
    // userspace passed us a bad allow number.
    match saved_slice.get(allow_num) {
        Some(saved) => {
            // Replace old values with current buffer.
            let (old, changed) = saved
                .value
                .try_replace(core::ptr::slice_from_raw_parts(ptr, len), unallow_previous);

            // Rotate liveness so any references still in the kernel become invalid
            if changed && unallow_previous {
                *saved.live.take_borrow() += 1;
            }

            (
                old.as_ptr(),
                old.len(),
                if !changed {
                    Err(ErrorCode::BUSY)
                } else {
                    Ok(())
                },
            )
        }
        None => (ptr, len, Err(ErrorCode::NOSUPPORT)),
    }
}

/// Stores the specified read-only process buffer in the kernel managed grant
/// region for this process and driver. The previous read-only process buffer
/// stored at the same allow_num id is returned.
#[inline(always)]
pub(crate) fn allow_ro(
    process: &dyn Process,
    driver_num: usize,
    allow_num: usize,
    buffer: ReadOnlyProcessBuffer,
) -> Result<ReadOnlyProcessBuffer, (ReadOnlyProcessBuffer, ErrorCode)> {
    let (ptr, len, proc) = buffer.consume();
    let unallow = (ptr as usize) == 0;
    // # Safety
    //
    // The ReadOnlyProcessBuffer type guarantees validity
    unsafe {
        let (ptr, len, result) =
            allow_helper(process, driver_num, allow_num, ptr, len, true, unallow);
        let buffer = ReadOnlyProcessBuffer::new_option(ptr, len, proc);
        match result {
            // The pointer has already been validated to be within application
            // memory before storing the values in the saved slice.
            Ok(()) => Ok(buffer),
            Err(code) => Err((buffer, code)),
        }
    }
}

/// Stores the specified read-write process buffer in the kernel managed grant
/// region for this process and driver. The previous read-write process buffer
/// stored at the same allow_num id is returned.
#[inline(always)]
pub(crate) fn allow_rw(
    process: &dyn Process,
    driver_num: usize,
    allow_num: usize,
    buffer: ReadWriteProcessBuffer,
) -> Result<ReadWriteProcessBuffer, (ReadWriteProcessBuffer, ErrorCode)> {
    let (ptr, len, proc) = buffer.consume();
    let unallow = (ptr as usize) == 0;

    // # Safety
    //
    // The ReadWriteProcessBuffer type guarantees validity
    unsafe {
        let (ptr, len, result) =
            allow_helper(process, driver_num, allow_num, ptr, len, false, unallow);
        let buffer = ReadWriteProcessBuffer::new_option(ptr as *mut u8, len, proc);
        match result {
            // The pointer has already been validated to be within application
            // memory before storing the values in the saved slice.
            Ok(()) => Ok(buffer),
            Err(code) => Err((buffer, code)),
        }
    }
}

/// An instance of a grant allocated for a particular process.
///
/// `ProcessGrant` is a handle to an instance of a grant that has been allocated
/// in a specific process's grant region. A `ProcessGrant` guarantees that the
/// memory for the grant has been allocated in the process's memory.
///
/// This is created from a `Grant` when that grant is entered for a specific
/// process.
pub struct ProcessGrant<'a, T, Upcalls: UpcallSize, AllowROs: AllowRoSize, AllowRWs: AllowRwSize> {
    /// The process entry for the process the grant is applied to.
    /// Must point to a valid entry for the lifetime of this struct
    process: &'static ProcEntry,

    /// The grant mem for the process. If this ProcessGrant is successfully created, this memory
    /// is initialised and valid for at least the lifetime of this object.
    grant_mem: NonNull<u8>,

    /// The syscall driver number this grant is associated with.
    driver_num: usize,

    /// Used to store Rust types for grant.
    _phantom: PhantomData<(T, Upcalls, AllowROs, AllowRWs, &'a dyn Process)>,
}

impl<'a, T: Default, Upcalls: UpcallSize, AllowROs: AllowRoSize, AllowRWs: AllowRwSize>
    ProcessGrant<'a, T, Upcalls, AllowROs, AllowRWs>
{
    /// Create a `ProcessGrant` for the given Grant in the given Process's grant
    /// region.
    ///
    /// If the grant in this process has not been setup before this will attempt
    /// to allocate the memory from the process's grant region.
    ///
    /// # Return
    ///
    /// If the grant is already allocated or could be allocated, and the process
    /// is valid, this returns `Ok(ProcessGrant)`. Otherwise it returns a
    /// relevant error.
    fn new(
        grant: &Grant<T, Upcalls, AllowROs, AllowRWs>,
        processid: ProcessId,
    ) -> Result<Self, Error> {
        // Moves non-generic code from new() into non-generic function to reduce
        // code bloat from the generic function being monomorphized, as it is
        // common to have over 50 copies of Grant::enter() in a Tock kernel (and
        // thus 50+ copies of this function). The returned Option indicates if
        // the returned pointer still needs to be initialized (in the case where
        // the grant was only just allocated).
        fn new_inner<'a>(
            grant_num: usize,
            driver_num: usize,
            grant_t_size: GrantDataSize,
            grant_t_align: GrantDataAlign,
            num_upcalls: UpcallItems,
            num_allow_ros: AllowRoItems,
            num_allow_rws: AllowRwItems,
            processid: ProcessId,
        ) -> Result<(Option<NonNull<u8>>, &'a ProcEntry, NonNull<u8>), Error> {
            // Here is an example of how the grants are laid out in the grant
            // region of process's memory:
            //
            // Mem. Addr.
            // 0x0040000  ┌────────────────────────────────────
            //            │   DriverNumN    [0x1]
            //            │   GrantPointerN [0x003FFC8]
            //            │   ...
            //            │   DriverNum1    [0x60000]
            //            │   GrantPointer1 [0x003FFC0]
            //            │   DriverNum0
            //            │   GrantPointer0 [0x0000000 (NULL)]
            //            ├────────────────────────────────────
            //            │   Process Control Block
            // 0x003FFE0  ├────────────────────────────────────  Grant Region ┐
            //            │   GrantDataN                                      │
            // 0x003FFC8  ├────────────────────────────────────               │
            //            │   GrantData1                                      ▼
            // 0x003FF20  ├────────────────────────────────────
            //            │
            //            │   --unallocated--
            //            │
            //            └────────────────────────────────────
            //
            // An array of pointers (one per possible grant region) point to
            // where the actual grant memory is allocated inside of the process.
            // The grant memory is not allocated until the actual grant region
            // is actually used.

            let process_entry = processid
                .kernel
                .get_process_entry(processid)
                .ok_or(Error::NoSuchApp)?;

            let process = process_entry.proc_ref.get().ok_or(Error::NoSuchApp)?;

            let grant_ptr = process.get_grant_mem(grant_num)?;

            match grant_ptr {
                None => {
                    // Calculate the alignment and size for entire grant region.
                    let alloc_align = EnteredGrantKernelManagedLayout::grant_align(grant_t_align);
                    let alloc_size = EnteredGrantKernelManagedLayout::grant_size(
                        num_upcalls,
                        num_allow_ros,
                        num_allow_rws,
                        grant_t_size,
                        grant_t_align,
                    );

                    // Allocate grant, the memory is still uninitialized though.
                    let grant_ptr = process
                        .allocate_grant(grant_num, driver_num, alloc_size, alloc_align)
                        .ok_or(Error::OutOfMemory)?;

                    // Create a layout from the counts we have and initialize
                    // all memory so it is valid in the future to read as a
                    // reference.
                    //
                    // # Safety
                    //
                    // - The grant base pointer is well aligned, yet does not
                    //   have initialized data.
                    // - The pointer points to a large enough space to correctly
                    //   write to is guaranteed by alloc of size
                    //   `EnteredGrantKernelManagedLayout::grant_size`.
                    // - There are no proper rust references that map to these
                    //   addresses.
                    unsafe {
                        let _layout = EnteredGrantKernelManagedLayout::initialize_from_counts(
                            grant_ptr,
                            num_upcalls,
                            num_allow_ros,
                            num_allow_rws,
                            process,
                            grant_num,
                        );
                        EnteredGrantKernelManagedLayout::get_grant_data_t_ref(grant_ptr)
                            .as_ptr()
                            .write(RefCell::new(Cell::new(false)));
                    }

                    // # Safety
                    //
                    // The grant pointer points to an alloc that is alloc_size
                    // large and is at least as aligned as grant_t_align.
                    unsafe {
                        Ok((
                            Some(EnteredGrantKernelManagedLayout::get_grant_data_t(
                                grant_ptr,
                                alloc_size,
                                grant_t_size,
                            )),
                            process_entry,
                            grant_ptr,
                        ))
                    }
                }
                Some(grant_ptr) => {
                    // T was already allocated, outer function should not
                    // initialize T.
                    Ok((None, process_entry, grant_ptr))
                }
            }
        }

        // Handle the bulk of the work in a function which is not templated.
        let (opt_raw_grant_ptr_nn, process_entry, grant_ptr) = new_inner(
            grant.grant_num,
            grant.driver_num,
            GrantDataSize(size_of::<T>()),
            GrantDataAlign(align_of::<T>()),
            UpcallItems(Upcalls::COUNT),
            AllowRoItems(AllowROs::COUNT),
            AllowRwItems(AllowRWs::COUNT),
            processid,
        )?;

        // We can now do the initialization of T object if necessary.
        match opt_raw_grant_ptr_nn {
            Some(allocated_ptr) => {
                // Grant type T
                //
                // # Safety
                //
                // This is safe because:
                //
                // 1. The pointer address is valid. The pointer is allocated
                //    statically in process memory, and will exist for as long
                //    as the process does. The grant is only accessible while
                //    the process is still valid.
                //
                // 2. The pointer is correctly aligned. The newly allocated
                //    grant is aligned for type T, and there is padding inserted
                //    between the upcall array and the T object such that the T
                //    object starts a multiple of `align_of<T>` from the
                //    beginning of the allocation.
                unsafe {
                    // Convert untyped `*mut u8` allocation to allocated type.
                    let new_region = NonNull::cast::<T>(allocated_ptr);
                    // We use `ptr::write` to avoid `Drop`ping the uninitialized
                    // memory in case `T` implements the `Drop` trait.
                    write(new_region.as_ptr(), T::default());
                }
            }
            None => {} // Case if grant was already allocated.
        }

        // We have ensured the grant is already allocated or was just allocated,
        // so we can create and return the `ProcessGrant` type.
        Ok(ProcessGrant {
            process: process_entry,
            grant_mem: grant_ptr,
            driver_num: grant.driver_num,
            _phantom: PhantomData,
        })
    }

    /// Return an `ProcessGrant` for a grant in a process if the process is
    /// valid and that process grant has already been allocated, or `None`
    /// otherwise.
    /// SAFETY: Must call with a valid process entry
    unsafe fn new_if_allocated(
        grant: &Grant<T, Upcalls, AllowROs, AllowRWs>,
        process: &'static ProcEntry,
    ) -> Option<Self> {
        if let Ok(Some(ptr)) = process
            .proc_ref
            .get()
            .unwrap_unchecked()
            .get_grant_mem(grant.grant_num)
        {
            Some(ProcessGrant {
                process: process,
                grant_mem: ptr,
                driver_num: grant.driver_num,
                _phantom: PhantomData,
            })
        } else {
            // Grant has not been allocated.
            // or Process is invalid.
            None
        }
    }

    /// We use a reference here because instances of `ProcessGrant` are very
    /// short lived. They only exist while a `Grant` is being entered or borrowed, so we can
    /// be sure the process still exists while a `ProcessGrant` exists. No
    /// `ProcessGrant` can be stored.
    #[inline]
    fn process_ref(&self) -> &'a dyn Process {
        unsafe {
            // Safety: these are only created for valid process entries
            self.process.proc_ref.get().unwrap_unchecked()
        }
    }

    /// Return the ProcessId of the process this ProcessGrant is associated with.
    #[inline]
    pub fn processid(&self) -> ProcessId {
        self.process_ref().processid()
    }

    /// Run a function with access to the memory in the related process for the
    /// related Grant. This also provides access to any associated Upcalls and
    /// allowed buffers stored with the grant.
    ///
    /// This is "entering" the grant region, and the _only_ time when the
    /// contents of a grant region can be accessed.
    ///
    /// Note, a grant can only be entered once at a time. Attempting to call
    /// `.enter()` on a grant while it is already entered will result in a
    /// panic!()`. See the comment in `access_grant()` for more information.
    pub fn enter<F, R>(self, fun: F) -> R
    where
        F: FnOnce(&mut GrantData<T>, &GrantKernelData) -> R,
    {
        // # `unwrap()` Safety
        //
        // `access_grant()` can only return `None` if the grant is already
        // entered. Since we are asking for a panic!() if the grant is entered,
        // `access_grant()` function will never return `None`.
        self.access_grant(fun, true).unwrap()
    }

    /// Run a function with access to the data in the related process for the
    /// related Grant only if that grant region is not already entered. If the
    /// grant is already entered silently skip it. Also provide access to
    /// associated Upcalls.
    ///
    /// **You almost certainly should use `.enter()` rather than
    /// `.try_enter()`.**
    ///
    /// While the `.enter()` version can panic, that panic likely indicates a
    /// bug in the code and not a condition that should be handled. For example,
    /// this benign looking code is wrong:
    ///
    /// ```ignore
    /// self.apps.enter(thisapp, |app_grant, _| {
    ///     // Update state in the grant region of `thisapp`. Also, mark that
    ///     // `thisapp` needs to run again.
    ///     app_grant.runnable = true;
    ///
    ///     // Now, check all apps to see if any are ready to run.
    ///     let mut work_left_to_do = false;
    ///     self.apps.iter().each(|other_app| {
    ///         other_app.enter(|other_app_grant, _| { // ERROR! This leads to a
    ///             if other_app_grant.runnable {      // grant being entered
    ///                 work_left_to_do = true;        // twice!
    ///             }
    ///         })
    ///     })
    /// })
    /// ```
    ///
    /// The example is wrong because it tries to iterate across all grant
    /// regions while one of them is already entered. This will lead to a grant
    /// region being entered twice which violates Rust's memory restrictions and
    /// is undefined behavior.
    ///
    /// However, since the example uses `.enter()` on the iteration, Tock will
    /// panic when the grant is entered for the second time, notifying the
    /// developer that something is wrong. The fix is to exit out of the first
    /// `.enter()` before attempting to iterate over the grant for all
    /// processes.
    ///
    /// However, if the example used `.try_enter()` in the iter loop, there
    /// would be no panic, but the already entered grant would be silently
    /// skipped. This can hide subtle bugs if the skipped grant is only relevant
    /// in certain cases.
    ///
    /// Therefore, only use `try_enter()` if you are sure you want to skip the
    /// already entered grant. Cases for this are rare.
    ///
    /// ## Return
    ///
    /// Returns `None` if the grant is already entered. Otherwise returns
    /// `Some(fun())`.
    pub fn try_enter<F, R>(self, fun: F) -> Option<R>
    where
        F: FnOnce(&mut GrantData<T>, &GrantKernelData) -> R,
    {
        self.access_grant(fun, false)
    }

    /// Run a function with access to the memory in the related process for the
    /// related Grant. Also provide this function with access to any associated
    /// Upcalls and an allocator for allocating additional memory in the
    /// process's grant region.
    ///
    /// This is "entering" the grant region, and the _only_ time when the
    /// contents of a grant region can be accessed.
    ///
    /// Note, a grant can only be entered once at a time. Attempting to call
    /// `.enter()` on a grant while it is already entered will result in a
    /// panic!()`. See the comment in `access_grant()` for more information.
    pub fn enter_with_allocator<F, R>(self, fun: F) -> R
    where
        F: FnOnce(&mut GrantData<T>, &GrantKernelData, &mut GrantRegionAllocator) -> R,
    {
        // # `unwrap()` Safety
        //
        // `access_grant()` can only return `None` if the grant is already
        // entered. Since we are asking for a panic!() if the grant is entered,
        // `access_grant()` function will never return `None`.
        self.access_grant_with_allocator(fun, true).unwrap()
    }

    /// Access the `ProcessGrant` memory and run a closure on the process's
    /// grant memory.
    ///
    /// If `panic_on_reenter` is `true`, this will panic if the grant region is
    /// already currently entered. If `panic_on_reenter` is `false`, this will
    /// return `None` if the grant region is entered and do nothing.
    fn access_grant<F, R>(self, fun: F, panic_on_reenter: bool) -> Option<R>
    where
        F: FnOnce(&mut GrantData<T>, &GrantKernelData) -> R,
    {
        self.access_grant_with_allocator(
            |grant_data, kernel_data, _allocator| fun(grant_data, kernel_data),
            panic_on_reenter,
        )
    }

    /// Access the `ProcessGrant` memory and run a closure on the process's
    /// grant memory.
    ///
    /// If `panic_on_reenter` is `true`, this will panic if the grant region is
    /// already currently entered. If `panic_on_reenter` is `false`, this will
    /// return `None` if the grant region is entered and do nothing.
    fn access_grant_with_allocator<F, R>(self, fun: F, panic_on_reenter: bool) -> Option<R>
    where
        F: FnOnce(&mut GrantData<T>, &GrantKernelData, &mut GrantRegionAllocator) -> R,
    {
        // Setup an allocator in case the capsule needs additional memory in the
        // grant space.
        let mut allocator = GrantRegionAllocator {
            processid: self.processid(),
        };

        // Get grant data
        let grant_data = self.get_grant_data();

        // Create a wrapped objects that are passed to functor.
        let mut kernel_data = self.get_kern_data();

        // Use legacy enter
        grant_data.legacy_enter(fun, panic_on_reenter, &mut kernel_data, &mut allocator)
    }

    /// Note: self is borrowed as these structs contain raw process references which must not be
    /// used across process lifetines.
    pub fn get_grant_data(&self) -> NewGrantData<'a, T> {
        // Access the grant T that is in process memory. Cannot fail, as a process grant would not
        // be created if the process were not already allocated.
        let grant_ptr = self.grant_mem;

        let grant_t_align = GrantDataAlign(align_of::<T>());
        let grant_t_size = GrantDataSize(size_of::<T>());

        let alloc_size = EnteredGrantKernelManagedLayout::grant_size(
            UpcallItems(Upcalls::COUNT),
            AllowRoItems(AllowROs::COUNT),
            AllowRwItems(AllowRWs::COUNT),
            grant_t_size,
            grant_t_align,
        );

        let grant_data_ptr: NonNull<T> = unsafe {
            EnteredGrantKernelManagedLayout::get_grant_data_t(grant_ptr, alloc_size, grant_t_size)
        }
        .cast::<T>();

        unsafe {
            NewGrantData::new(
                EnteredGrantKernelManagedLayout::get_grant_data_t_ref(grant_ptr).as_ref(),
                grant_data_ptr,
                self.process,
            )
        }
    }

    #[inline]
    pub fn get_kern_data(&self) -> GrantKernelData<'a> {
        let grant_ptr = self.grant_mem;
        let process = self.process_ref();
        let grant_num = unsafe {
            process
                .lookup_grant_from_driver_num(self.driver_num)
                .unwrap_unchecked()
        };

        // Determine layout of entire grant alloc
        //
        // # Safety
        //
        // Grant pointer is well aligned and points to initialized data.
        let layout = unsafe {
            EnteredGrantKernelManagedLayout::read_from_base(grant_ptr, process, grant_num)
        };

        // Get references to all of the saved upcall data.
        //
        // # Safety
        //
        // - Pointer is well aligned and initialized with data from Self::new()
        //   call.
        // - Data will not be modified externally while this immutable reference
        //   is alive.
        // - Data is accessible for the entire duration of this immutable
        //   reference.
        let saved_upcalls_slice =
            unsafe { slice::from_raw_parts(layout.upcalls_array, Upcalls::COUNT.into()) };
        let saved_allow_ro_slice =
            unsafe { slice::from_raw_parts(layout.allow_ro_array, AllowROs::COUNT.into()) };
        let saved_allow_rw_slice =
            unsafe { slice::from_raw_parts(layout.allow_rw_array, AllowRWs::COUNT.into()) };

        GrantKernelData::new(
            saved_upcalls_slice,
            saved_allow_ro_slice,
            saved_allow_rw_slice,
            self.driver_num,
            // We would not have created this process grant if the process was NONE.
            unsafe { self.process.proc_ref.get().unwrap_unchecked() },
        )
    }
}

/// Grant which was allocated from the kernel-owned grant region in a specific
/// process's memory, separately from a normal `Grant`.
///
/// A `CustomGrant` allows a capsule to allocate additional memory on behalf of
/// a process.
pub struct CustomGrant<T> {
    /// An identifier for this custom grant within a process's grant region.
    ///
    /// Here, this is an opaque reference that Process uses to access the
    /// custom grant allocation. This setup ensures that Process owns the grant
    /// memory.
    identifier: ProcessCustomGrantIdentifier,

    /// Identifier for the process where this custom grant is allocated.
    processid: ProcessId,

    /// Used to keep the Rust type of the grant.
    _phantom: PhantomData<T>,
}

impl<T> CustomGrant<T> {
    /// Creates a new `CustomGrant`.
    fn new(identifier: ProcessCustomGrantIdentifier, processid: ProcessId) -> Self {
        CustomGrant {
            identifier,
            processid,
            _phantom: PhantomData,
        }
    }

    /// Helper function to get the ProcessId from the custom grant.
    pub fn processid(&self) -> ProcessId {
        self.processid
    }

    /// Gives access to inner data within the given closure.
    ///
    /// If the process has since been restarted or crashed, or the memory is
    /// otherwise no longer present, then this function will not call the given
    /// closure, and will instead directly return `Err(Error::NoSuchApp)`.
    ///
    /// Because this function requires `&mut self`, it should be impossible to
    /// access the inner data of a given `CustomGrant` reentrantly. Thus the
    /// reentrance detection we use for non-custom grants is not needed here.
    pub fn enter<F, R>(&mut self, fun: F) -> Result<R, Error>
    where
        F: FnOnce(GrantData<'_, T>) -> R,
    {
        // Verify that the process this CustomGrant was allocated within still
        // exists.
        self.processid
            .kernel
            .process_map_or(Err(Error::NoSuchApp), self.processid, |process| {
                // App is valid.

                // Now try to access the custom grant memory.
                let grant_ptr = process.enter_custom_grant(self.identifier)?;

                // # Safety
                //
                // `grant_ptr` must be a valid pointer and there must not exist
                // any other references to the same memory. We verify the
                // pointer is valid and aligned when the memory is allocated and
                // `CustomGrant` is created. We are sure that there are no
                // other references because the only way to create a reference
                // is using this `enter()` function, and it can only be called
                // once (because of the `&mut self` requirement).
                let custom_grant = unsafe { GrantData::new(&mut *(grant_ptr as *mut T)) };

                Ok(fun(custom_grant))
            })
    }
}

/// Tool for allocating additional memory regions in a process's grant region.
///
/// This is optionally provided along with a grant so that if a capsule needs
/// per-process dynamic allocation it can allocate additional memory.
pub struct GrantRegionAllocator {
    /// The process the allocator will allocate memory from.
    processid: ProcessId,
}

impl GrantRegionAllocator {
    // FIXME: Include the RefCell here

    /// Allocates a new `CustomGrant` initialized using the given closure.
    ///
    /// The closure will be called exactly once, and the result will be used to
    /// initialize the owned value.
    ///
    /// This interface was chosen instead of a simple `alloc(val)` as it's
    /// much more likely to optimize out all stack intermediates. This
    /// helps to prevent stack overflows when allocating large values.
    ///
    /// # Panic Safety
    ///
    /// If `init` panics, the freshly allocated memory may leak.
    pub fn alloc_with<T, F>(&mut self, init: F) -> Result<CustomGrant<T>, Error>
    where
        F: FnOnce() -> T,
    {
        let (custom_grant_identifier, typed_ptr) = self.alloc_raw::<T>()?;

        // # Safety
        //
        // Writing to this pointer is safe as long as the pointer is valid
        // and aligned. `alloc_raw()` guarantees these constraints are met.
        unsafe {
            // We use `ptr::write` to avoid `Drop`ping the uninitialized memory
            // in case `T` implements the `Drop` trait.
            write(typed_ptr.as_ptr(), init());
        }

        Ok(CustomGrant::new(custom_grant_identifier, self.processid))
    }

    /// Allocates a slice of n instances of a given type. Each instance is
    /// initialized using the provided function.
    ///
    /// The provided function will be called exactly `n` times, and will be
    /// passed the index it's initializing, from `0` through `NUM_ITEMS - 1`.
    ///
    /// # Panic Safety
    ///
    /// If `val_func` panics, the freshly allocated memory and any values
    /// already written will be leaked.
    pub fn alloc_n_with<T, F, const NUM_ITEMS: usize>(
        &mut self,
        mut init: F,
    ) -> Result<CustomGrant<[T; NUM_ITEMS]>, Error>
    where
        F: FnMut(usize) -> T,
    {
        let (custom_grant_identifier, typed_ptr) = self.alloc_n_raw::<T>(NUM_ITEMS)?;

        for i in 0..NUM_ITEMS {
            // # Safety
            //
            // The allocate function guarantees that `ptr` points to memory
            // large enough to allocate `num_items` copies of the object.
            unsafe {
                write(typed_ptr.as_ptr().add(i), init(i));
            }
        }

        Ok(CustomGrant::new(custom_grant_identifier, self.processid))
    }

    /// Allocates uninitialized grant memory appropriate to store a `T`.
    ///
    /// The caller must initialize the memory.
    ///
    /// Also returns a ProcessCustomGrantIdentifier to access the memory later.
    fn alloc_raw<T>(&mut self) -> Result<(ProcessCustomGrantIdentifier, NonNull<T>), Error> {
        self.alloc_n_raw::<T>(1)
    }

    /// Allocates space for a dynamic number of items.
    ///
    /// The caller is responsible for initializing the returned memory.
    ///
    /// Returns memory appropriate for storing `num_items` contiguous instances
    /// of `T` and a ProcessCustomGrantIdentifier to access the memory later.
    fn alloc_n_raw<T>(
        &mut self,
        num_items: usize,
    ) -> Result<(ProcessCustomGrantIdentifier, NonNull<T>), Error> {
        let (custom_grant_identifier, raw_ptr) =
            self.alloc_n_raw_inner(num_items, size_of::<T>(), align_of::<T>())?;
        let typed_ptr = NonNull::cast::<T>(raw_ptr);

        Ok((custom_grant_identifier, typed_ptr))
    }

    /// Helper to reduce code bloat by avoiding monomorphization.
    fn alloc_n_raw_inner(
        &mut self,
        num_items: usize,
        single_alloc_size: usize,
        alloc_align: usize,
    ) -> Result<(ProcessCustomGrantIdentifier, NonNull<u8>), Error> {
        let alloc_size = single_alloc_size
            .checked_mul(num_items)
            .ok_or(Error::OutOfMemory)?;
        self.processid
            .kernel
            .process_map_or(Err(Error::NoSuchApp), self.processid, |process| {
                process
                    .allocate_custom_grant(alloc_size, alloc_align)
                    .map_or(
                        Err(Error::OutOfMemory),
                        |(custom_grant_identifier, raw_ptr)| Ok((custom_grant_identifier, raw_ptr)),
                    )
            })
    }
}

/// Type for storing an object of type T in process memory that is only
/// accessible by the kernel.
///
/// A single `Grant` can allocate space for one object of type T for each
/// process on the board. Each allocated object will reside in the grant region
/// belonging to the process that the object is allocated for. The `Grant` type
/// is used to get access to `ProcessGrant`s, which are tied to a specific
/// process and provide access to the memory object allocated for that process.
pub struct Grant<T: Default, Upcalls: UpcallSize, AllowROs: AllowRoSize, AllowRWs: AllowRwSize> {
    /// Hold a reference to the core kernel so we can iterate processes.
    pub(crate) kernel: &'static Kernel,

    /// Keep track of the syscall driver number assigned to the capsule that is
    /// using this grant. This allows us to uniquely identify upcalls stored in
    /// this grant.
    driver_num: usize,

    /// The identifier for this grant. Having an identifier allows the Process
    /// implementation to lookup the memory for this grant in the specific
    /// process.
    grant_num: usize,

    /// Used to store the Rust types for grant.
    ptr: PhantomData<(T, Upcalls, AllowROs, AllowRWs)>,
}

impl<T: Default, Upcalls: UpcallSize, AllowROs: AllowRoSize, AllowRWs: AllowRwSize>
    Grant<T, Upcalls, AllowROs, AllowRWs>
{
    /// Create a new `Grant` type which allows a capsule to store
    /// process-specific data for each process in the process's memory region.
    ///
    /// This must only be called from the main kernel so that it can ensure that
    /// `grant_index` is a valid index.
    pub(crate) const fn new(
        kernel: &'static Kernel,
        driver_num: usize,
        grant_index: usize,
    ) -> Self {
        Self {
            kernel: kernel,
            driver_num: driver_num,
            grant_num: grant_index,
            ptr: PhantomData,
        }
    }

    pub fn get_for(
        &self,
        processid: ProcessId,
    ) -> Result<ProcessGrant<'_, T, Upcalls, AllowROs, AllowRWs>, Error> {
        ProcessGrant::new(self, processid)
    }

    /// Enter the grant for a specific process.
    ///
    /// This creates a `ProcessGrant` which is a handle for a grant allocated
    /// for a specific process. Then, that `ProcessGrant` is entered and the
    /// provided closure is run with access to the memory in the grant region.
    pub fn enter<F, R>(&self, processid: ProcessId, fun: F) -> Result<R, Error>
    where
        F: FnOnce(&mut GrantData<T>, &GrantKernelData) -> R,
    {
        let pg = ProcessGrant::new(self, processid)?;

        // If we have managed to create an `ProcessGrant`, all we need
        // to do is actually access the memory and run the
        // capsule-provided closure. This can only fail if the grant is
        // already entered, at which point the kernel will panic.
        Ok(pg.enter(fun))
    }

    /// Enter the grant for a specific process, or if it is the same as processid_inside, use the
    /// provided grant data instead
    pub fn enter_or_reenter<F, R>(
        &self,
        processid: ProcessId,
        processid_inside: ProcessId,
        grant_data_inside: &mut GrantData<T>,
        grant_kernel_data_inside: &GrantKernelData,
        fun: F,
    ) -> Result<R, Error>
    where
        F: FnOnce(&mut GrantData<T>, &GrantKernelData) -> R,
    {
        if processid != processid_inside {
            self.enter(processid, fun)
        } else {
            Ok(fun(grant_data_inside, grant_kernel_data_inside))
        }
    }

    /// Enter the grant for a specific process with access to an allocator.
    ///
    /// This creates an `ProcessGrant` which is a handle for a grant allocated
    /// for a specific process. Then, that `ProcessGrant` is entered and the
    /// provided closure is run with access to the memory in the grant region.
    ///
    /// The allocator allows the caller to dynamically allocate additional
    /// memory in the process's grant region.
    pub fn enter_with_allocator<F, R>(&self, processid: ProcessId, fun: F) -> Result<R, Error>
    where
        F: FnOnce(&mut GrantData<T>, &GrantKernelData, &mut GrantRegionAllocator) -> R,
    {
        // Get the `ProcessGrant` for the process, possibly needing to
        // actually allocate the memory in the process's grant region to
        // do so. This can fail for a variety of reasons, and if so we
        // return the error to the capsule.
        let pg = ProcessGrant::new(self, processid)?;

        // If we have managed to create an `ProcessGrant`, all we need
        // to do is actually access the memory and run the
        // capsule-provided closure. This can only fail if the grant is
        // already entered, at which point the kernel will panic.
        Ok(pg.enter_with_allocator(fun))
    }

    /// Run a function on the grant for each active process if the grant has
    /// been allocated for that process.
    ///
    /// This will silently skip any process where the grant has not previously
    /// been allocated. This will also silently skip any invalid processes.
    ///
    /// Calling this function when an `ProcessGrant` for a process is currently
    /// entered will result in a panic.
    pub fn each<F>(&self, mut fun: F)
    where
        F: FnMut(ProcessId, &mut GrantData<T>, &GrantKernelData),
    {
        // Create a the iterator across `ProcessGrant`s for each process.
        for pg in self.iter() {
            let processid = pg.processid();
            // Since we iterating, there is no return value we need to worry
            // about.
            pg.enter(|data, upcalls| fun(processid, data, upcalls));
        }
    }

    /// Get an iterator over all processes and their active grant regions for
    /// this particular grant.
    ///
    /// Calling this function when an `ProcessGrant` for a process is currently
    /// entered will result in a panic.
    pub fn iter(
        &self,
    ) -> Iter<T, Upcalls, AllowROs, AllowRWs, impl Iterator<Item = &'static ProcEntry>> {
        Iter {
            grant: self,
            subiter: self.kernel.get_proc_entry_iter(),
        }
    }
}

/// Type to iterate `ProcessGrant`s across processes.
pub struct Iter<
    'a,
    T: 'a + Default,
    Upcalls: UpcallSize,
    AllowROs: AllowRoSize,
    AllowRWs: AllowRwSize,
    SubIter: Iterator<Item = &'static ProcEntry>,
> {
    /// The grant type to use.
    grant: &'a Grant<T, Upcalls, AllowROs, AllowRWs>,

    /// Iterator over valid processes.
    subiter: SubIter,
}

impl<
        'a,
        T: Default,
        Upcalls: UpcallSize,
        AllowROs: AllowRoSize,
        AllowRWs: AllowRwSize,
        SubIter: Iterator<Item = &'static ProcEntry>,
    > Iterator for Iter<'a, T, Upcalls, AllowROs, AllowRWs, SubIter>
{
    type Item = ProcessGrant<'a, T, Upcalls, AllowROs, AllowRWs>;

    fn next(&mut self) -> Option<Self::Item> {
        let grant = self.grant;
        // Get the next `ProcessId` from the kernel processes array that is
        // setup to use this grant. Since the iterator itself is saved calling
        // this function again will start where we left off.
        // SAFETY: subiter will only provide valid process entrys
        unsafe {
            self.subiter
                .find_map(|process| ProcessGrant::new_if_allocated(grant, process))
        }
    }
}

/// A liveness tracker for a process
#[derive(Copy, Clone)]
pub struct PLiveTracker {
    /// Comparing to the usize in this reference reveals whether 'r' should still exist
    compare_to: &'static crate::kernel::ProcEntry,
    /// What the value should be
    compare: usize,
}

/// Strictly, this should never roll-over in order to ensure safety (for the user).
/// However, if we are happy with a probabilistic defense we could make this smaller for a given
/// build.
type ATrackerInt = usize;

/// A liveness tracker for a single allowed ro/rw buffer or callback
/// Must be paired with a PLiveTracker, as grants are no longer valid upon process death.
#[derive(Copy, Clone)]
pub struct ALiveTracker {
    compare_to: NonNull<Cell<ATrackerInt>>,
    compare: ATrackerInt,
}

impl PartialEq for PLiveTracker {
    fn eq(&self, other: &Self) -> bool {
        (self.compare_to as *const crate::kernel::ProcEntry
            == other.compare_to as *const crate::kernel::ProcEntry)
            && (self.compare == other.compare)
    }
}

impl PartialEq for ALiveTracker {
    fn eq(&self, other: &Self) -> bool {
        self.compare_to.eq(&other.compare_to) && (self.compare == other.compare)
    }
}

// To make non-pref types fit in with pref.
static DUMMY_ENTRY: ProcEntry = ProcEntry {
    valid_proc_id: Cell::new(0),
    proc_ref: Cell::new(None),
};
struct TrackerIntWrapper(Cell<ATrackerInt>);

// We can imagine the kernel as one large grant that will never be out of lifetime
static KERNEL_GRANT: TrackerIntWrapper = TrackerIntWrapper(Cell::new(0 as ATrackerInt));

// Tock is single threaded
unsafe impl Sync for ProcEntry {}
unsafe impl Sync for TrackerIntWrapper {}

fn get_dummy_entry() -> &'static ProcEntry {
    &DUMMY_ENTRY
}
fn get_kernel_grant() -> &'static Cell<ATrackerInt> {
    &KERNEL_GRANT.0
}

/// Can verify whether a reference is still valid.
/// If it is, it will continue to be valid in the scope it was verified.
pub trait Track: Copy + Clone + PartialEq {
    /// Safety: implementors may have requirements on where this gets called
    unsafe fn is_still_alive(&self) -> bool;

    fn global_live() -> Self;
    fn global_dead() -> Self;
}

impl PLiveTracker {
    #[inline]
    pub fn new(with_proc: &'static crate::kernel::ProcEntry) -> Self {
        Self::new_with_id(with_proc, with_proc.valid_proc_id.get())
    }

    #[inline]
    pub fn new_with_id(with_proc: &'static crate::kernel::ProcEntry, id: usize) -> Self {
        Self {
            compare_to: with_proc,
            compare: id,
        }
    }

    #[inline]
    pub(crate) fn get_proc(&self) -> Option<&'static dyn process::Process> {
        if unsafe { self.is_still_alive() } {
            self.compare_to.proc_ref.get()
        } else {
            None
        }
    }
}

impl Track for PLiveTracker {
    #[inline]
    unsafe fn is_still_alive(&self) -> bool {
        self.compare == (*self.compare_to).valid_proc_id.get()
    }

    #[inline]
    fn global_live() -> Self {
        // 0 is the expected value of the entry.
        Self::new_with_id(get_dummy_entry(), 0)
    }

    #[inline]
    fn global_dead() -> Self {
        // 0 is the expected value of the entry. Any non-zero value would do here.
        Self::new_with_id(get_dummy_entry(), 1)
    }
}

impl ALiveTracker {
    #[inline]
    pub fn new(track: &Cell<ATrackerInt>) -> Self {
        Self::new_with_compare(track, track.get())
    }

    #[inline]
    pub fn new_with_compare(track: &Cell<ATrackerInt>, compare: ATrackerInt) -> Self {
        Self {
            compare_to: NonNull::from(track),
            compare,
        }
    }
}

impl Track for ALiveTracker {
    /// Safety: can only be called AFTER the process has been checked for liveness
    #[inline]
    unsafe fn is_still_alive(&self) -> bool {
        unsafe { self.compare_to.as_ref().get() == self.compare }
    }

    #[inline]
    fn global_live() -> Self {
        Self::new_with_compare(get_kernel_grant(), 0)
    }

    #[inline]
    fn global_dead() -> Self {
        Self::new_with_compare(get_kernel_grant(), 1)
    }
}

/// Both a tracker for process liveness, and allow liveness.
#[derive(Copy, Clone, PartialEq)]
pub struct DualTracker {
    ptracker: PLiveTracker,
    atracker: ALiveTracker,
}

impl DualTracker {
    pub fn new(ptracker: PLiveTracker, atracker: ALiveTracker) -> Self {
        Self { ptracker, atracker }
    }
    pub(crate) fn get_proc(&self) -> Option<&'static dyn process::Process> {
        let result = self.ptracker.get_proc()?;
        unsafe {
            if !self.atracker.is_still_alive() {
                return None;
            }
        }
        Some(result)
    }
}

impl Track for DualTracker {
    #[inline]
    unsafe fn is_still_alive(&self) -> bool {
        // Safety: if the process is still alive, it is then safe to check the allow for liveness
        self.ptracker.is_still_alive() && self.atracker.is_still_alive()
    }

    fn global_live() -> Self {
        Self::new(PLiveTracker::global_live(), ALiveTracker::global_live())
    }

    fn global_dead() -> Self {
        Self::new(PLiveTracker::global_dead(), ALiveTracker::global_live())
    }
}

/// A (shared) reference to a T that exists for as long as a specific tracker does.
/// We offer a cloneable and non-cloneable version.
/// The second is useful as it can be safely converted to/from &'static mut.
pub struct PRefBase<T: ?Sized, Trk: Track, const CLONE: bool> {
    r: NonNull<T>,
    tracker: Trk,
}

pub type PRef<T> = PRefBase<T, PLiveTracker, true>;
pub type PRefNoClone<T> = PRefBase<T, PLiveTracker, false>;

pub type ARef<T> = PRefBase<T, DualTracker, true>;
pub type ARefNoClone<T> = PRefBase<T, DualTracker, false>;

impl<T: ?Sized, Trk: Track> Clone for PRefBase<T, Trk, true> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}
impl<T: ?Sized, Trk: Track> Copy for PRefBase<T, Trk, true> {}

/// Same as a `PRef<T>` but has been checked for liveness in a scope in which a process will never
/// be de-allocated.
/// Derefs into `&T`
#[repr(transparent)]
pub struct LivePRefBase<'a, T: ?Sized, Trk: Track, const CLONE: bool> {
    r: PRefBase<T, Trk, CLONE>,
    _phantom: PhantomData<&'a T>,
}

pub type LivePRef<'a, T> = LivePRefBase<'a, T, PLiveTracker, true>;
pub type LivePRefNoClone<'a, T> = LivePRefBase<'a, T, PLiveTracker, false>;
pub type LiveARef<'a, T> = LivePRefBase<'a, T, DualTracker, true>;
pub type LiveARefNoClone<'a, T> = LivePRefBase<'a, T, DualTracker, false>;

impl<'a, T: ?Sized, Trk: Track> Clone for LivePRefBase<'a, T, Trk, true> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}
impl<'a, T: ?Sized, Trk: Track> Copy for LivePRefBase<'a, T, Trk, true> {}

impl<T> Default for PRef<T> {
    fn default() -> Self {
        Self {
            r: NonNull::dangling(),
            tracker: PLiveTracker::global_dead(),
        }
    }
}

fn zero_sized_dangling() -> NonNull<[u8]> {
    NonNull::slice_from_raw_parts(NonNull::dangling(), 0)
}

// Defaults for the process slices to make it easier to have values before initialization.
// The default PRef is global dead to a zero-length slice
// The default LivePRef is a global live to a zero-length slice

impl<const CLONE: bool> Default for PRefBase<ReadableProcessSlice, DualTracker, CLONE> {
    fn default() -> Self {
        // SAFETY: safe to transmute from [u8] to ReadableProcessSlice for purpose of a dangling
        // reference
        unsafe {
            Self {
                r: core::mem::transmute(zero_sized_dangling()),
                tracker: DualTracker::global_dead(),
            }
        }
    }
}

impl<const CLONE: bool> Default for PRefBase<WriteableProcessSlice, DualTracker, CLONE> {
    fn default() -> Self {
        // SAFETY: safe to transmute from [u8] to WriteableProcessSlice for purpose of a dangling
        // reference
        unsafe {
            Self {
                r: core::mem::transmute(zero_sized_dangling()),
                tracker: DualTracker::global_dead(),
            }
        }
    }
}

impl<'a, const CLONE: bool> Default for LivePRefBase<'a, ReadableProcessSlice, DualTracker, CLONE> {
    fn default() -> Self {
        // SAFETY: safe to transmute from [u8] to ReadableProcessSlice for purpose of a dangling
        // reference
        unsafe {
            Self {
                r: PRefBase::<ReadableProcessSlice, DualTracker, CLONE> {
                    r: core::mem::transmute(zero_sized_dangling()),
                    tracker: DualTracker::global_live(),
                },
                _phantom: Default::default(),
            }
        }
    }
}

impl<'a, const CLONE: bool> Default
    for LivePRefBase<'a, WriteableProcessSlice, DualTracker, CLONE>
{
    fn default() -> Self {
        // SAFETY: safe to transmute from [u8] to WriteableProcessSlice for purpose of a dangling
        // reference
        unsafe {
            Self {
                r: PRefBase::<WriteableProcessSlice, DualTracker, CLONE> {
                    r: core::mem::transmute(zero_sized_dangling()),
                    tracker: DualTracker::global_live(),
                },
                _phantom: Default::default(),
            }
        }
    }
}

impl<T: ?Sized, const CLONE: bool> PRefBase<T, PLiveTracker, CLONE> {
    /// Safety: the caller guarantees this data would be valid to cast to a shared reference as
    /// long as the ProcEntry keeps its ID the same.
    #[inline]
    pub(crate) unsafe fn new(
        data: NonNull<T>,
        with_proc: &'static crate::kernel::ProcEntry,
    ) -> Self {
        Self::new_with_tracker(data, PLiveTracker::new(with_proc))
    }

    /// Get a ProcessID for this PRef.
    /// This always succeeds, but the resulting ProcessID may be invalid.
    /// PRef does not contain a kernel reference to keep them small so the caller must provide it.
    #[inline]
    pub fn get_process_id(&self, kernel: &'static Kernel) -> ProcessId {
        ProcessId::new(
            kernel,
            self.tracker.compare,
            // Note: if this is the DUMMY_ENTRY, then the index will always be
            // invalid and so the process ID will return None when index is called.
            kernel.index_of_proc_entry(self.tracker.compare_to),
        )
    }
}

impl<T: ?Sized, Trk: Track, const CLONE: bool> PRefBase<T, Trk, CLONE> {
    #[inline]
    pub unsafe fn as_ref_unchecked(&self) -> &T {
        self.r.as_ref()
    }

    /// Get the raw pointer from this PRef. It is only safe to dereference it if the tracker is
    /// valid.
    #[inline]
    pub fn get_ptr(&self) -> NonNull<T> {
        self.r
    }

    /// To allow code to be authored once for both user buffers and kernel buffers, we can think
    /// of the kernel as process 0 with static lifetime and one large allow
    pub fn new_from_static(data: &'static T) -> Self {
        // Safety: types that ascribe to static will always be live.
        unsafe { Self::new_with_tracker(data.into(), Trk::global_live()) }
    }

    pub fn try_unwrap_static(self) -> Result<&'static T, ()> {
        if self.tracker.eq(&Trk::global_live()) {
            Ok(unsafe {
                // Safety: the only time we use the global_live tracker is the method above where
                // the reference was originally a static ref.
                self.r.as_ref()
            })
        } else {
            Err(())
        }
    }

    /// Safety: the caller guarantees this data would be valid for as long as the tracker returns
    /// true.
    pub(crate) unsafe fn new_with_tracker(data: NonNull<T>, tracker: Trk) -> Self {
        Self { r: data, tracker }
    }

    #[inline]
    pub fn is_still_alive(&self) -> bool {
        unsafe { self.tracker.is_still_alive() }
    }

    /// A different version of try_into_live that also works with non-cloneable references
    /// Prefer try_into_live().
    #[inline]
    pub fn with_live<R, F: FnOnce(Option<LivePRefBase<T, Trk, CLONE>>) -> R>(self, f: F) -> R {
        let option_live = if self.is_still_alive() {
            Some(LivePRefBase {
                r: self,
                _phantom: PhantomData,
            })
        } else {
            None
        };
        f(option_live)
    }

    /// Unchecked version of try_into_live. The caller guarantees bounding the lifetime 'a
    #[inline]
    pub unsafe fn into_live_unchecked<'a>(self) -> LivePRefBase<'a, T, Trk, CLONE> {
        LivePRefBase {
            r: self,
            _phantom: PhantomData,
        }
    }

    /// Are the _pointers_ equal (not what they point to)
    #[inline]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        self.r == other.r && self.tracker == other.tracker
    }
}

impl<T: ?Sized, Trk: Track> PRefBase<T, Trk, true> {
    /// Get a lifetime bounded version of the reference. Will return None if the process has been
    /// freed since this reference was created.
    /// This on its own is safe to call, but should only be done so from a context where a process
    /// cannot be reclaim-ed. The actual "Unsafe" part is whatever does that, and should take care
    /// not to have any LivePRef types AT ALL in scope, nor be callable from any context that does.
    /// The way that is guaranteed is to have such reclaims only be done from the main kernel loop,
    /// and having calling the main kernel loop be unsafe with that invariant.
    #[inline]
    pub fn try_into_live(&self) -> Option<LivePRefBase<T, Trk, true>> {
        if self.is_still_alive() {
            Some(LivePRefBase {
                r: *self,
                _phantom: PhantomData,
            })
        } else {
            None
        }
    }

    /// Borrow as live without allocating a new object.
    /// See try_into_live.
    #[inline]
    pub fn try_borrow_live(&self) -> Option<&LivePRefBase<T, Trk, true>> {
        if self.is_still_alive() {
            Some(
                // Safety: LivePRefBase is a transparent wrapper around PRefBase with the
                // only added invariant that it has been checked for liveness (which we
                // have just done)
                // Because the type is immutable (through a non-mut reference) this cannot
                // change.
                unsafe { core::mem::transmute(self) },
            )
        } else {
            None
        }
    }

    pub fn as_noclone(self) -> PRefBase<T, Trk, false> {
        PRefBase {
            r: self.r,
            tracker: self.tracker,
        }
    }
}

impl<T: ?Sized, Trk: Track> PRefBase<T, Trk, false> {
    /// Like new_from_static, we can consider the kernel a special process 0 with static lifetime.
    pub fn new_from_static_mut(data: &'static mut T) -> Self {
        // Safety: types that ascribe to static will always be live.
        // This version of PRef cannot be cloned, so also obeys the requirements.
        unsafe { Self::new_with_tracker(data.into(), Trk::global_live()) }
    }

    pub fn try_unwrap_static_mut(mut self) -> Result<&'static mut T, ()> {
        if self.tracker.eq(&Trk::global_live()) {
            Ok(unsafe {
                // Safety: the only time we use the global_live tracker is the method above where
                // the reference was originally a static ref.
                // Because we never allowed this to be cloned, it is OK to still be mut.
                self.r.as_mut()
            })
        } else {
            Err(())
        }
    }
}

// Convert from &'static mut [u8] to a type that is similar to what might come from userspace.
// Allows same code path for both userspace and kernel
impl From<&'static mut [u8]> for ARefNoClone<ReadableProcessSlice> {
    fn from(value: &'static mut [u8]) -> Self {
        let as_pref = ARefNoClone::<[u8]>::new_from_static_mut(value);
        // Safety: We originally had a &mut[u8], so a <[Cell<u8>]> is safe to transmute to.
        unsafe { transmute(as_pref) }
    }
}

// Convert back. If this was not actually a &'static mut ref originally, we get a zero-length
// slice.
impl From<ARefNoClone<ReadableProcessSlice>> for &'static mut [u8] {
    fn from(value: ARefNoClone<ReadableProcessSlice>) -> Self {
        match value.try_unwrap_static_mut() {
            Ok(proc_slice) => {
                // SAFETY: the fact we just unwrapped from a PRefNoClone means that this was constructed
                // from a mutable reference using new_from_static_mut. It is therefore safe to upgrade
                // to a mut.
                unsafe { transmute(proc_slice) }
            }
            Err(_) => {
                // Safety: is valid for all 0 reads a zero slice would allow
                unsafe { zero_sized_dangling().as_mut() }
            }
        }
    }
}

impl<T: ?Sized, Trk: Track> From<&'static T> for PRefBase<T, Trk, true> {
    #[inline]
    fn from(value: &'static T) -> Self {
        PRefBase::new_from_static(value)
    }
}

impl<T: ?Sized, Trk: Track> From<&'static mut T> for PRefBase<T, Trk, false> {
    fn from(value: &'static mut T) -> Self {
        PRefBase::new_from_static_mut(value)
    }
}

// We can always convert back to the type that needs checking later
impl<'a, T: ?Sized, Trk: Track, const CLONE: bool> From<LivePRefBase<'a, T, Trk, CLONE>>
    for PRefBase<T, Trk, CLONE>
{
    #[inline]
    fn from(live: LivePRefBase<'a, T, Trk, CLONE>) -> Self {
        live.r
    }
}

// Converting to a live reference may fail
impl<'a, T: ?Sized, Trk: Track> TryFrom<&'a PRefBase<T, Trk, true>>
    for LivePRefBase<'a, T, Trk, true>
{
    type Error = ();

    fn try_from(value: &'a PRefBase<T, Trk, true>) -> Result<Self, Self::Error> {
        value.try_into_live().ok_or(())
    }
}

// The live variant can be dereferenced freely
impl<'a, T: ?Sized, Trk: Track, const CLONE: bool> Deref for LivePRefBase<'a, T, Trk, CLONE> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        // SAFETY: The lifetime on this reference is guaranteed by the kernel to not cover a
        // process being freed.
        unsafe { self.r.as_ref_unchecked() }
    }
}

impl<'a, T: ?Sized, Trk: Track, const CLONE: bool> LivePRefBase<'a, T, Trk, CLONE> {
    /// Safety: the new reference must have a lifetime less than or equal to the old one
    #[inline]
    unsafe fn with_new_ref<U: ?Sized>(self, new: &U) -> LivePRefBase<'a, U, Trk, CLONE> {
        LivePRefBase {
            r: PRefBase::new_with_tracker(NonNull::from(new), self.r.tracker),
            _phantom: PhantomData,
        }
    }

    #[inline]
    pub fn map<U: ?Sized, F: FnOnce(&T) -> &U>(
        orig: Self,
        f: F,
    ) -> LivePRefBase<'a, U, Trk, CLONE> {
        unsafe {
            // Safe to cast to reference as this type guarantees the process is still live
            let r = orig.r.r.as_ref();
            // Safety: f gives the guarantee for with_new_ref
            orig.with_new_ref(f(r))
        }
    }
}

impl<'a, T: ?Sized, const CLONE: bool> LivePRefBase<'a, T, DualTracker, CLONE> {
    /// Safety: the caller guarantees this data would be valid to cast to a shared reference as
    /// long as the ProcEntry keeps its ID the same and the tracker does not change
    #[inline]
    pub(crate) unsafe fn new(
        data: NonNull<T>,
        proc_tracker: PLiveTracker,
        allow_tracker: &Cell<ATrackerInt>,
    ) -> Self {
        Self {
            r: PRefBase::new_with_tracker(
                data,
                DualTracker::new(proc_tracker, ALiveTracker::new(allow_tracker)),
            ),
            _phantom: PhantomData,
        }
    }
}

impl<'a, T: ?Sized, const CLONE: bool> LivePRefBase<'a, T, PLiveTracker, CLONE> {
    /// Safety: the caller guarantees this data would be valid to cast to a shared reference as
    /// long as the ProcEntry keeps its ID the same AND that the process is currently live.
    #[inline]
    pub unsafe fn new(data: NonNull<T>, with_proc: &'static crate::kernel::ProcEntry) -> Self {
        Self {
            r: PRefBase::new(data, with_proc),
            _phantom: PhantomData,
        }
    }

    #[inline]
    /// See get_process_id for PRef
    pub fn get_process_id(&self, kernel: &'static Kernel) -> ProcessId {
        self.r.get_process_id(kernel)
    }
}

impl<'a, T: ?Sized, Trk: Track> LivePRefBase<'a, T, Trk, true> {
    #[inline]
    pub fn map_split<U: ?Sized, V: ?Sized, F: FnOnce(&T) -> (&U, &V)>(
        orig: Self,
        f: F,
    ) -> (
        LivePRefBase<'a, U, Trk, true>,
        LivePRefBase<'a, V, Trk, true>,
    ) {
        let split = f(orig.deref());
        unsafe { (orig.with_new_ref(split.0), orig.with_new_ref(split.1)) }
    }

    #[inline]
    pub fn as_noclone(self) -> LivePRefBase<'a, T, Trk, false> {
        LivePRefBase {
            r: self.r.as_noclone(),
            _phantom: self._phantom,
        }
    }
}

impl<T: ?Sized, Trk: Track> PanicDeref for PRefBase<T, Trk, true> {
    type Target = T;

    /// This should be avoided in favour of try_into_live. This is provided
    /// for interfaces that assume they are otherwise ensuring that the
    /// PRef can only ever be live, but need this checked.
    fn panic_deref(&self) -> &Self::Target {
        if !self.is_still_alive() {
            panic!()
        }
        unsafe { self.as_ref_unchecked() }
    }
}

// Blanket implementation of important traits

// Length
impl<T: ?Sized, Trk: Track, const COPY: bool> BufLength for PRefBase<T, Trk, COPY>
where
    NonNull<T>: BufLength,
{
    fn buf_len(&self) -> usize {
        self.get_ptr().buf_len()
    }
}

#[cfg(test)]
mod tests {
    use crate::collections::list::PanicDeref;
    use crate::grant::{LivePRef, PLiveTracker, PRef, Track};
    use crate::kernel::ID_INVALID;
    use crate::ProcEntry;
    use core::cell::Cell;
    use core::ops::Deref;
    use core::ptr::NonNull;
    use std::mem::transmute;

    // Tests of the PBuf types. NOTE: This does not test the core kernel allocation logic for now as
    // that is very tied up with process logic.
    // Instead, this tries to test the PRef<T> as standalone types.

    // A proc entry for testing. Normally, this would be from the main process array.
    thread_local! {
        static TEST_PROC_ENTRY: ProcEntry = const { ProcEntry {
            valid_proc_id: Cell::new(0),
            proc_ref: Cell::new(None),
        }};
    }

    // This is only for testing. Normally, the kernel would guarantee no LivePRefs exist when this
    // is changed. Tests should maintain that.
    fn change_test_id(id: usize) {
        TEST_PROC_ENTRY.with(|entry| entry.valid_proc_id.set(id));
    }

    // Construct a PRef<T> for testing. Normally, the NonNull would be provided by the grant
    // allocator.
    // This is only for testing. The caller should ensure that ptr never aliases with a mutable
    // reference and stays in lifetime for the duration of the test.
    fn make_test_pref<T>(ptr: NonNull<T>) -> PRef<T> {
        TEST_PROC_ENTRY.with(|entry| unsafe { PRef::new(ptr, transmute(entry)) })
    }

    #[test]
    fn simple_test() {
        // Mock process creation:
        change_test_id(1);

        // Allocation.
        let some_val: u32 = 123;
        let r = make_test_pref(NonNull::from(&some_val));

        // Can be converted in PRefLives
        {
            // Returns an option as it might fail
            let as_live = r.try_into_live();
            // Unwrap should succeed at this point
            let as_live = as_live.unwrap();
            // Can be used as a &u32
            assert_eq!(*as_live, 123);
        }

        // Mock process destruction
        change_test_id(ID_INVALID);

        // Can trying to convert into live again:
        {
            let as_live = r.try_into_live();
            // But it will fail as the process no longer exists
            assert!(as_live.is_none());
        }
    }

    struct LessBoringType {
        first: u32,
        second: u32,
    }

    #[test]
    fn test_mapping_and_conversion() {
        // Mock process creation:
        change_test_id(1);

        let some_val = LessBoringType {
            first: 66,
            second: 77,
        };

        let r = make_test_pref(NonNull::from(&some_val));
        let r_first: PRef<u32>;
        {
            let as_live = r.try_into_live().unwrap();
            // Accessing items is easy:
            assert_eq!(as_live.first, 66);
            assert_eq!(as_live.second, 77);
            // However, a reference like:
            let _normal_ref: &u32 = &as_live.deref().first;
            // Is legal to construct, but has a limited lifetime that might not be flexible enough.
            // Instead, use map can obtain a LivePRef to something like a member
            let mapped_ref: LivePRef<u32> = LivePRef::map(as_live, |r| &r.first);
            // And a like pref can be converted back to PRef, which has a more flexible lifetime
            r_first = mapped_ref.into();
        }

        let pair: (PRef<u32>, PRef<u32>);

        // map_split can be used (possibly multiple times) to extract multiple references
        {
            let as_live = r.try_into_live().unwrap();
            let split = LivePRef::map_split(as_live, |r| (&r.first, &r.second));
            pair = (split.0.into(), split.1.into());
        }

        // All the PRefs can be used again while the process is live...
        {
            assert_eq!(*r_first.try_into_live().unwrap(), 66);
            assert_eq!(*pair.0.try_into_live().unwrap(), 66);
            assert_eq!(*pair.1.try_into_live().unwrap(), 77);
        }

        // Mock process destruction
        change_test_id(ID_INVALID);

        // ...but stop working after
        {
            assert!(r_first.try_into_live().is_none());
            assert!(pair.0.try_into_live().is_none());
            assert!(pair.1.try_into_live().is_none());
        }
    }

    static SOME_GLOBAL: u32 = 7;

    #[test]
    fn misc_lifetimes() {
        // We could consider the kernel as a process that never dies
        let static_ref = &SOME_GLOBAL;
        // So if code expects a PRef and you want to pass a global static, this exists:
        let as_pref = PRef::new_from_static(static_ref);
        assert_eq!(*as_pref.try_into_live().unwrap(), 7);
        // Such a PRef will is always alive.

        // Rather than using Option<PRef> for a PRef that might not be there, a PRef can start out
        // dead. This is the default. It will never be alive.
        let default_pref: PRef<i32> = Default::default();
        assert!(default_pref.try_into_live().is_none());
    }

    #[test]
    fn trackers() {
        // PRef uses a tracker to check if it is live. If you want to make your own types that
        // track process liveness, they are available:

        // Always alive
        let live_tracker = PLiveTracker::global_live();
        assert!(unsafe { live_tracker.is_still_alive() });

        // Always dead
        let live_tracker = PLiveTracker::global_dead();
        assert!(unsafe { !live_tracker.is_still_alive() });

        // Tracks a process:
        change_test_id(1);
        unsafe {
            unsafe fn with_id(id: usize) -> PLiveTracker {
                TEST_PROC_ENTRY.with(|entry| PLiveTracker::new_with_id(transmute(entry), id))
            }

            let live_tracker1 = with_id(1);
            let live_tracker2 = with_id(2);

            assert!(live_tracker1.is_still_alive());
            assert!(!live_tracker2.is_still_alive());

            change_test_id(ID_INVALID);

            assert!(!live_tracker1.is_still_alive());
            assert!(!live_tracker2.is_still_alive());
        }
    }

    #[test]
    #[should_panic]
    fn test_panic() {
        change_test_id(1);
        let some_val: u32 = 123;
        let r = make_test_pref(NonNull::from(&some_val));
        change_test_id(ID_INVALID);
        r.panic_deref();
    }
}
