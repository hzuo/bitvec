use core::{
	marker::PhantomData,
	mem::ManuallyDrop,
	pin::Pin,
	sync::atomic::Ordering,
};

use radium::Radium;
use tap::Pipe;

use super::BitRcHandle;
use crate::{
	array::BitArray,
	boxed::BitBox,
	order::BitOrder,
	ptr::BitSpan,
	slice::BitSlice,
	store::BitStore,
	view::BitViewSized,
};

impl<R, O, T> BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	/// Constructs a new ref-counted bit-slice from a bit-array.
	///
	/// NOTE: There will probably never be a distinction between the use of this
	/// method and using a standard-library `Rc<BitArray>` or `Arc<BitArray>`.
	///
	/// This type exists to provide `Rc<BitSlice>`, which the standard library
	/// cannot represent. The standard library API for `Rc<[bool]>` is to use
	/// `<Rc<[bool]> as From<&[bool]>>::from`, and so [`BitRcHandle::from`] is
	/// the correct equivalent for copying an arbitrary `&BitSlice` into a
	/// refcounted buffer.
	///
	/// # Original
	///
	/// [`Rc::new`](alloc::rc::Rc::new)
	///
	/// # Parameters
	///
	/// - `value`: Some bit-slice to copy into a new, ref-counted, buffer.
	///
	/// # Returns
	///
	/// A handle to a new ref-counted bit-slice buffer. This handle may be
	/// cheaply [`Clone`]d and, if `R` is atomic, passed between threads.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::rc::BitRc;
	///
	/// let five = BitRc::new(bitarr!(Lsb0, u8; 1, 0, 0, 1));
	/// ```
	///
	/// [`BitArray`]: crate::array::BitArray
	/// [`Clone`]: core::clone::Clone
	#[inline]
	pub fn new<V>(value: BitArray<O, V>) -> Self
	where V: BitViewSized<Store = T> {
		Self::new_from_bitspan(value.as_bitspan())
	}

	/// Constructs a new `Pin<BitRcHandle<BitSlice<O, T>>>`. Since `BitSlice` is
	/// `Unpin`, this has no consequences.
	///
	/// # Original
	///
	/// [`Rc::pin`](alloc::rc::Rc::pin)
	#[inline]
	pub fn pin<V>(value: BitArray<O, V>) -> Pin<Self>
	where V: BitViewSized<Store = T> {
		Pin::new(Self::new(value))
	}

	/// Returns the inner value, if the `BitRcHandle` has exactly one reference.
	///
	/// Otherwise, an [`Err`] is returned with the same `BitRcHandle` that was
	/// passed in.
	///
	/// # Original
	///
	/// [`Rc::try_unwrap`](alloc::rc::Rc::try_unwrap)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::rc::BitRc;
	///
	/// let boxed = bitbox![1, 0, 1, 1, 0, 0, 1, 0];
	///
	/// let rc = BitRc::from(&*boxed);
	/// assert_eq!(BitRc::try_unwrap(rc), Ok(boxed.clone()));
	///
	/// let rc2 = BitRc::from(&*boxed);
	/// let rc3 = BitRc::clone(&rc2);
	/// assert_eq!(BitRc::try_unwrap(rc2), Err(rc3));
	/// ```
	#[inline]
	pub fn try_unwrap(this: Self) -> Result<BitBox<O, T::Unalias>, Self> {
		if this.is_unique() {
			Ok(this
				.pipe_ref(Self::as_bitslice)
				.to_bitvec()
				.into_boxed_bitslice())
		}
		else {
			Err(this)
		}
	}

	/// Consumes the `BitRcHandle`, returning the wrapped `BitSlice` pointer.
	///
	/// To avoid a memory leak the pointer must be converted back into a
	/// `BitRcHandle` using [`BitRcHandle::from_raw`].
	///
	/// # Original
	///
	/// [`Rc::into_raw`](alloc::rc::Rc::into_raw)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::rc::BitRc;
	///
	/// let x = BitRc::from(bits![1, 0, 0, 1, 0]);
	/// let x_ptr = BitRc::into_raw(x);
	/// assert_eq!(unsafe { &*x_ptr }, bits![1, 0, 0, 1, 0]);
	/// ```
	#[inline]
	pub fn into_raw(this: Self) -> *const BitSlice<O, T> {
		ManuallyDrop::new(this).span.to_bitslice_ptr()
	}

	#[doc(hidden)]
	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	#[deprecated = "Use `as_bitslice_ptr` to access the region pointer"]
	pub fn as_ptr(this: &Self) -> *const BitSlice<O, T> {
		Self::as_bitslice_ptr(this)
	}

	/// Constructs a `BitRcHandle` from a raw pointer.
	///
	/// The raw pointer must have been previously returned by a call to
	/// [`BitRcHandle::into_raw`].
	///
	/// This function is unsafe because improper use may lead to memory
	/// unsafety, even if the returned `BitRcHandle` is never accessed.
	///
	/// # Original
	///
	/// [`Rc::from_raw`](alloc::rc::Rc::from_raw)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::rc::BitRc;
	///
	/// let x = BitRc::from(bits![1, 0, 1, 1, 0]);
	/// let x_ptr = BitRc::into_raw(x);
	///
	/// unsafe {
	///     // Convert back to a `BitRc` to prevent leak.
	///     let x = BitRc::from_raw(x_ptr);
	///     assert_eq!(&*x, bits![1, 0, 1, 1, 0]);
	///
	///     // Further calls to `BitRc::from_raw(x_ptr)` would be memory-unsafe.
	/// }
	///
	/// // The memory was freed when `x` went out of scope above, so `x_ptr` is now dangling!
	/// ```
	#[inline]
	#[allow(clippy::missing_safety_doc)]
	pub unsafe fn from_raw(ptr: *const BitSlice<O, T>) -> Self {
		Self {
			span: BitSpan::from_bitslice_ptr_mut(ptr as *mut _),
			_rad: PhantomData,
		}
	}

	/// Creates a new `BitRcHandle`.
	///
	/// # Original
	///
	/// [`Rc::downgrade`](alloc::rc::Rc::downgrade)
	///
	/// # API Differences
	///
	/// `BitRcHandle` does not have a concept of weak pointers, as `BitSlice` is
	/// always initialized and there is no difference between holding an
	/// allocation that may be used to contain a `BitSlice` and holding an
	/// allocated `BitSlice`. As such, this is merely a synonym for `Clone`.
	///
	/// The type aliases `BitRcWeak` and `BitArcWeak` map to `BitRc` and
	/// `BitArc`, respectively, so that you can continue using these patterns.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::rc::BitRc;
	///
	/// let rc: BitRc = BitRc::from(bits![1, 0, 1, 1, 0]);
	/// let weak: BitRc = BitRc::downgrade(&rc);
	/// // no effect at all.
	/// ```
	#[inline]
	#[cfg(not(tarpaulin_include))]
	pub fn downgrade(this: &Self) -> Self {
		Self::clone(this)
	}

	/// Upgrades a weak ref-counted pointer into a strong ref-counted pointer.
	///
	/// `BitRcHandle` does not distinguish weak and strong references! This
	/// always succeeds, and is kept only for API compatibility.
	///
	/// # Original
	///
	/// [`rc::Weak::upgrade`] and [`sync::Weak::upgrade`].
	///
	/// # API Differences
	///
	/// `BitRcWeak` and `BitArcWeak` are type aliases over `BitRcHandle`. This
	/// has no effect.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::rc::{BitRc, BitRcWeak};
	///
	/// let rc: BitRc = BitRc::from(bits![1, 1, 0, 1, 0]);
	/// let weak: BitRcWeak = BitRc::downgrade(&rc);
	/// let strong: BitRc = BitRcWeak::upgrade(&weak).unwrap();
	/// // `BitRcWeak` is an alias to `BitRc`.
	/// ```
	///
	/// [`sync::Weak::upgrade`]: alloc::sync::Weak::upgrade
	/// [`rc::Weak::upgrade`]: alloc::rc::Weak::upgrade
	#[inline]
	#[cfg(not(tarpaulin_include))]
	pub fn upgrade(this: &Self) -> Option<Self> {
		Some(Self::clone(this))
	}

	/// Gets the number of weak pointers to this allocation.
	///
	/// Weak pointers keep the allocation alive while the contents are dead.
	/// `BitSlice` regions are by definition always initialized and alive, so
	/// weak pointers are not relevant here.
	///
	/// # Original
	///
	/// [`Rc::weak_count`](alloc::rc::Rc::weak_count)
	#[doc(hidden)]
	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	#[deprecated = "`BitRcHandle` has no weak pointers"]
	pub fn weak_count(_: &Self) -> usize {
		0
	}

	/// Gets the number of strong pointers to this allocation.
	///
	/// # Original
	///
	/// [`Rc::strong_count`](alloc::rc::Rc::strong_count)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::rc::BitRc;
	///
	/// let rc = BitRc::from(bits![1; 10]);
	/// let rc2 = BitRc::clone(&rc);
	/// assert_eq!(BitRc::strong_count(&rc2), 2);
	/// ```
	#[inline]
	pub fn strong_count(this: &Self) -> usize {
		this.refcount_slot().load(Ordering::Relaxed)
	}

	/// Increments the refcount on the allocation associated with the provided
	/// pointer.
	///
	/// # Original
	///
	/// [`Arc::increment_strong_count`][isc]
	///
	/// # Safety
	///
	/// The pointer must have been obtained through [`BitArc::into_raw`], and
	/// the associated `BitArc` instance must be valid (i.e. the strong count
	/// must be at least 1) for the duration of this method.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::rc::BitArc;
	///
	/// let arc = BitArc::from(bits![1, 1, 0, 1, 0]);
	///
	/// unsafe {
	///   let bitptr = BitArc::into_raw(arc);
	///   BitArc::increment_strong_count(bitptr);
	///
	///   let arc2 = BitArc::from_raw(bitptr);
	///   assert_eq!(BitArc::strong_count(&arc2), 2);
	/// }
	/// ```
	///
	/// [isc]: alloc::sync::Arc::increment_strong_count
	/// [`BitArc::into_raw`]: Self::into_raw
	#[inline]
	pub unsafe fn increment_strong_count(ptr: *const BitSlice<O, T>) {
		Self::from_raw(ptr).pipe(ManuallyDrop::new).incr();
	}

	/// Decrements the refcount on the allocation associated with the provided
	/// pointer.
	///
	/// # Original
	///
	/// [`Arc::decrement_strong_count`][dsc]
	///
	/// # Safety
	///
	/// The pointer must have been obtained through [`BitArc::into_raw`], and
	/// the associated `BitArc` instance must be valid (i.e. the strong count
	/// must be at least 1) for the duration of this method.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::rc::BitArc;
	///
	/// let arc = BitArc::from(bits![1, 1, 0, 1, 0]);
	///
	/// unsafe {
	///   let bitptr = BitArc::into_raw(arc);
	///   BitArc::increment_strong_count(bitptr);
	///
	///   let arc2 = BitArc::from_raw(bitptr);
	///   assert_eq!(BitArc::strong_count(&arc2), 2);
	///   BitArc::decrement_strong_count(bitptr);
	///   assert_eq!(BitArc::strong_count(&arc2), 1);
	/// }
	/// ```
	///
	/// [dsc]: alloc::sync::Arc::decrement_strong_count
	/// [`BitArc::into_raw`]: Self::into_raw
	#[inline]
	pub unsafe fn decrement_strong_count(ptr: *const BitSlice<O, T>) {
		Self::from_raw(ptr).pipe(ManuallyDrop::new).decr();
	}

	/// Returns a mutable reference into the given `BitRcHandle`, if there are
	/// no other `BitRcHandle` pointers to the same allocation.
	///
	/// Returns [`None`] otherwise, because it is not safe to mutate a shared
	/// value.
	///
	/// # Original
	///
	/// [`Rc::get_mut`](alloc::rc::Rc::get_mut)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::rc::BitRc;
	///
	/// let mut rc = BitRc::from(bits![0; 5]);
	/// BitRc::get_mut(&mut rc).unwrap().store(0b10110u8);
	/// assert_eq!(
	///   *rc,
	///   &0b10110usize.view_bits::<Lsb0>()[..5],
	/// );
	#[inline]
	pub fn get_mut(this: &mut Self) -> Option<&mut BitSlice<O, T>> {
		if this.is_unique() {
			Some(this.span.to_bitslice_mut())
		}
		else {
			None
		}
	}

	/// Returns `true` if the two `BitRcHandle`s point to the same allocation
	/// (in a vein similar to [`ptr::eq`]).
	///
	/// # Original
	///
	/// [`Rc::ptr_eq`](alloc::rc::Rc::ptr_eq)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::rc::BitRc;
	///
	/// let rc = BitRc::from(bits![1, 0, 1, 1, 0]);
	/// let rc2 = BitRc::clone(&rc);
	/// let rc3 = BitRc::from(&*rc);
	///
	/// assert!(BitRc::ptr_eq(&rc, &rc2));
	/// assert!(!BitRc::ptr_eq(&rc2, &rc3));
	/// ```
	///
	/// [`ptr::eq`]: crate::ptr::eq
	#[inline]
	pub fn ptr_eq<T2>(this: &Self, that: &BitRcHandle<R, O, T2>) -> bool
	where T2: BitStore<Mem = T::Mem> {
		this.span == that.span
	}

	/// Makes a mutable reference into the given `BitRcHandle`.
	///
	/// If there are other handles to this allocation, then `make_mut` will copy
	/// the inner `BitSlice` into a new allocation to ensure unique ownership.
	/// This is also referred to as clone-on-write.
	///
	/// See also [`get_mut`], which will fail rather than copying to a new
	/// allocation.
	///
	/// # Original
	///
	/// [`Rc::make_mut`](alloc::rc::Rc::make_mut)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::rc::BitRc;
	///
	/// let mut rc1 = BitRc::from(bits![1, 0, 1, 1, 0]);
	///
	/// BitRc::make_mut(&mut rc1).set(4, true);  // Won't clone anything
	/// let mut rc2 = BitRc::clone(&rc1);        // Won't clone inner data
	/// BitRc::make_mut(&mut rc1).set(0, false); // Clones inner data
	/// BitRc::make_mut(&mut rc1).set(1, true);  // Won't clone anything
	/// BitRc::make_mut(&mut rc2).set(2, false); // Won't clone anything
	///
	/// // Now `rc1` and `rc2` point to different allocations.
	/// assert_eq!(rc1, bits![0, 1, 1, 1, 1]);
	/// assert_eq!(rc2, bits![1, 0, 0, 1, 1]);
	/// ```
	///
	/// [`get_mut`]: Self::get_mut
	#[inline]
	pub fn make_mut(this: &mut Self) -> &mut BitSlice<O, T> {
		if !this.is_unique() {
			*this = this.fork();
		}
		this.span.to_bitslice_mut()
	}
}
