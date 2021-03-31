/*! Reference-counted, heap-allocated, bit sequences.

The types [`BitRc<O, T>`][`BitRc`] and [`BitArc<O, T>`][`BitArc`] provide shared
ownership of a [`BitSlice<O, T>`][`BitSlice`] allocated in the heap. Invoking
[`clone`][Clone::clone] on `BitRc` or `BitArc` produces a new pointer to the
same allocation in the heap. When the last [`BitRc`] or [`BitArc`] pointer to a
given allocation is destroyed, the inner `BitSlice` and the allocation are also
dropped.

Shared references in Rust disallow mutation by default, and `BitRc`/`BitArc` are
no exception: you cannot generally obtain an `&mut BitSlice` to the contents. If
you need mutability, you can use the [`Cell`] or [`Atomic`] variants of
[`T: BitStore`] initially, or you can convert the bit-slice in-place with
[`BitRc::make_shared`](BitRcHandle::make_shared).

[`BitRc`] uses non-atomic reference counting. This means that the overhead is
very low, but a [`BitRc`] cannot be sent between threads, and consequently
[`BitRc`] does not implement [`Send`]. However, [`BitArc`] *does* use atomic
reference counting, which has costlier `Clone` and `Drop` behaviors, but can
cross threads and therefore is `Send`.

`BitRc` automatically dereferences to `BitSlice`, so you can call `BitSlice`
methods on it directly. In addition, it implements many of `BitSlice`’s traits,
including bitwise arithmetic, so that you can use these containers alongside the
others in the crate. `BitRc`’s own functions all require that you call them with
the [fully-qualified syntax][ufcs].

`BitRc`’s implementations of traits like `Clone` may also be called with
fully-qualified syntax. Some people prefer to use fully-qualified syntax, while
others prefer using method-call syntax.

```rust
use bitvec::prelude::*;
use bitvec::rc::BitRc;

let rc = BitRc::from(bits![1, 0, 1, 1, 0]);
let rc2 = BitRc::clone(&rc);
let rc3 = rc.clone();
```

# Cloning References

Creating a new reference to the same allocation as an existing reference-counted
pointer is done using the `Clone` trait implemented for [`BitRcHandle`]. The
example above creates two duplicates of `rc`, all of which point to the same
allocation. The fully-qualified syntax makes it easier to see that this code is
creating a new reference rather than cloning the interior `BitSlice` into a new
allocation.

> Note: `BitSlice` does not implement `Clone`, so method-call syntax is less of
> a concern, but [`BitBox`] and [`BitVec`] *do* implement `Clone` into new
> allocations, and so distinguishing ref-counting from full duplication may
> still be worthwhile.

# Original Types

[`Rc<[bool]>`](alloc::rc::Rc) and [`Arc<[bool]>`](alloc::sync::Arc)

# API Differences

The types in this module have a few key distinctions in API from their standard
library counterparts:

## `Radium` Parametricity

`BitRc` and `BitArc` are in fact merely partially-specialized type aliases over
the [`BitRcHandle`] type, which accepts a type parameter dictating whether it
uses atomic or non-atomic reference counting. This choice reflects that the two
standard library types have very nearly identical APIs, differing only in the
way they access their refcount; unlike the standard library, `bitvec` has access
to the [`radium`] crate’s trait-level atomicity and can use it to simplify such
API equivalences.

You should prefer to use the aliases rather than the base [`BitRcHandle`] type,
but the option is available.

## No `Weak` Pointers

The standard library provides [`Weak`] refcounting pointers that keep an
allocation alive, but do not keep the value *in* that allocation alive. This
distinction allows code that needs to know about a value, but can survive that
value’s destruction, to hold a pointer to an object’s location without taking an
ownership stake.

`BitSlice` has no ownership or liveness semantics. It is merely a region of
memory that has bits in it. Therefore, the types in this module do not have weak
variants at this time; all ref-counting pointers are equally able to access the
contained `BitSlice`.

> If you need `bitvec` to emulate the strong/weak distinction, please
> [file an issue][gh] and I will add them when I am able.

The functions that interact with `Weak` pointers are retained and have no
effect, and the type aliases [`BitRcWeak`] and [`BitArcWeak`] map to [`BitRc`]
and [`BitArc`], respectively.

# Use Cases

These pointers can only point to `BitSlice`s, not to any other, more complex,
types. As such, the semicyclic example in the standard library documentation
does not apply.

You can use these types to share read-only (when integer-typed) or
safely-writable (when `Cell`ed or atomic) bit-slice buffers between multiple
sections of your code without incurring lifetime constraints.

The `BitRc` type may *never* be shared between threads, and `BitArc` may only
be shared between threads when it contains `T: {integer}` (read-only) or
`T: {atomic}` (write-capable). `BitArc<_, Cell<u8>>` is, of course, not
thread-safe, just as `Arc<[Cell<bool>]>` is not.

# Prelude

This module is not included in the `bitvec` prelude, as `Rc` and `Arc` are not
in the `alloc` or `std` preludes.

[`Atomic`]: core::sync::atomic
[`BitArc`]: BitArc
[`BitArcWeak`]: BitArcWeak
[`BitBox`]: crate::boxed::BitBox
[`BitRc`]: BitRc
[`BitRcWeak`]: BitRcWeak
[`BitRcHandle`]: BitRcHandle
[`BitSlice`]: crate::slice::BitSlice
[`BitVec`]: crate::vec::BitVec
[`Cell`]: core::cell::Cell
[`T: BitStore`]: crate::store::BitStore
[`Weak`]: alloc::rc::Weak
[gh]: https://github.com/bitvecto-rs/bitvec/issues/new?title=Implement+%60rc::Weak%60&body=Please%20implement%20%60Weak%60%20pointers%20in%20%60bitvec%3A%3Arc%60.%0A%0A%3E%20This%20issue%20was%20autogenerated%20by%20the%20crate%20documentation.
[ufcs]: https://doc.rust-lang.org/book/ch19-03-advanced-traits.html#fully-qualified-syntax-for-disambiguation-calling-methods-with-the-same-name
!*/

#![cfg(feature = "alloc")]

#[cfg(not(feature = "std"))]
use alloc::vec;
use core::{
	cell::Cell,
	marker::PhantomData,
	mem::ManuallyDrop,
	ptr::{
		self,
		NonNull,
	},
	sync::atomic::Ordering,
};

use radium::{
	types::RadiumUsize,
	Radium,
};
use tap::Pipe;

use crate::{
	mem::elts,
	order::{
		BitOrder,
		Lsb0,
	},
	ptr::{
		AddressExt,
		BitSpan,
		Const,
		Mut,
	},
	slice::BitSlice,
	store::BitStore,
};

mod api;
mod ops;
mod traits;

/// A non-atomic [`BitRcHandle`].
pub type BitRc<O = Lsb0, T = usize> = BitRcHandle<Cell<usize>, O, T>;

/// A best-effort-atomic [`BitRcHandle`].
pub type BitArc<O = Lsb0, T = usize> = BitRcHandle<RadiumUsize, O, T>;

/// A non-atomic weak [`BitRcHandle`].
pub type BitRcWeak<O = Lsb0, T = usize> = BitRc<O, T>;

/// A best-effort-atomic weak [`BitRcHandle`].
pub type BitArcWeak<O = Lsb0, T = usize> = BitArc<O, T>;

/** Layout of the heap allocation to which refhandles point.

This is currently unused; handles are just `*mut BitSlice` pointers directly to
the region, and subtract one from the base address in order to reach the
refcount. This type is provided as documentation only.
**/
#[repr(C)]
#[allow(dead_code)]
struct BitRcBuffer<R, O = Lsb0, T = usize>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	/// `BitSlice` does not make a distinction between uninitialized and
	/// initialized. The bit-slice is always initialized, and because the buffer
	/// itself is frozen, its contents are always live. As such, this only needs
	/// to maintain one refcount and not distinguish between handles to the
	/// `BitSlice` region vs handles to the allocation.
	refcount: R,
	/// The region being shared.
	data: BitSlice<O, T>,
}

/** A sharing handle to a reference-counted, heap-allocated, [`BitSlice`].

The types [`BitRc<O, T>`] and [`BitArc<O, T>`] provide shared ownership of a
[`BitSlice<O, T>`][`BitSlice`] region, allocated in the heap. Invoking [`clone`]
on `BitRc` or `BitArc` produces a new instance, which points to the same
allocation on the heap as the source, while increasing a reference count. When
the last `BitRc` or `BitArc` pointer to a given allocation is destroyed, the
`BitSlice` stored in that location is also dropped.

Shared references in Rust disallow mutation by default, and `BitRc` and `BitArc`
are no exception: you cannot generally obtain a mutable reference to the
`BitSlice` inside them. If you need to mutate through a ref-count pointer, use
a [`Cell`] or [atomic] type parameter.

# Original

[`alloc::rc::Rc`] and [`alloc::sync::Arc`]

# API Differencess

This has two major differences from the standard library:

1. It is parametric over synchronization. You may choose whether to use
   [`Cell<usize>`][`Cell`] or [`AtomicUsize`][atomic] as the counter type at
   first construction.
1. It does not have a weak counter. Because [`BitSlice`] is always initialized,
   these handles do not need to distinguish between a live buffer and a dead,
   but still allocated, buffer.

# Type Aliases

For your convenience, the following type aliases are provided:

- [`BitRc<O, T>`]: `BitRcHandle<Cell<usize>, O, T>`
- [`BitArc<O, T>`]: `BitRcHandle<RadiumUsize, O, T>`
- [`BitRcWeak<O, T>`]: `BitRc<O, T>`
- [`BitArcWeak<O, T>`]: `BitArc<O, T>`

The `Arc` aliases use [`RadiumUsize`] so that they will gracefully decay on
targets that do not have `AtomicUsize` without breaking your build with a symbol
resolution failure.

# Thread Safety

Both `BitRc` of *any* `T: BitStore` type parameter, and `BitArc<_, Cell<_>>` are
unsafe to share across threads, as they use non-atomic operations to interact
with the allocation. `BitArc` uses atomic operations for its reference counting,
and `{integer}` and `{atomic}` `T: BitStore` parameters are safe to share across
threads.

The disadvantage of atomic operations in the refcount or `BitSlice` access is
that atomic operations are more temporally expensive than ordinary memory
accesses. If you are not sharing reference-counted allocations between threads,
use `BitRc` and either `{integer}` or `Cell<{integer}>` type parameters for
lower overhead. `BitRc` is a safe default, because the compiler will catch any
attempt to send a `BitRc` between threads.

`BitArc<_, T>` only implements [`Send`] and [`Sync`] when `T` is `Sync`. This,
combined with its unwillingness to give out `&mut BitSlice` references except
when the buffer is provably uniquely viewed, ensures that you cannot create data
races by attempting to write to the `BitSlice` without going through atomic
synchronization.

# Cloning References

Creating a new reference from an existing reference-counted pointer is done
using the `Clone` trait.

```rust
use bitvec::prelude::*;
use bitvec::rc::BitRc;

let rc = BitRc::from(bits![1, 0, 0, 1, 0]);
let rc2 = rc.clone();
let rc3 = BitRc::clone(&rc);
```

All three handles point to the same memory location.

# `Deref` Behavior and Method Calls

`BitRcHandle` dereferences to `BitSlice`, so all of `BitSlice`’s methods can be
called on it. In keeping with the standard library APIs, `BitRcHandle` defines
only associated functions, no methods of its own, so its inherents must always
be called using fully-qualified `BitRc::function(&name)` syntax.

Trait  implementations may still be called with `name.trait_method()`, but you
may wish to use fully-qualified syntax to make it clear that you are working on
the handle rather than the data.

# Additional Capabilities

Because `bitvec` has the ability to describe relationships between unshared and
shared mutable types, `BitRcHandle` offers [`make_shared`] and [`make_frozen`]
functions to cast the mutability permissions of the contained `BitSlice`, and
[`make_atomic`] and [`make_celled`] functions to select whether the refcount is
atomic or not.

These four functions all operate in-place when working on allocations that have
only one reference, and copy the `BitSlice` to a new allocation if it is already
shared.

[`BitArc<O, T>`]: BitArc
[`BitRc<O, T>`]: BitRc
[`BitSlice`]: crate::slice::BitSlice
[`Cell`]: core::cell::Cell
[`RadiumUsize`]: radium::types::RadiumUsize
[`clone`]: Clone::clone
[`make_atomic`]: Self::make_atomic
[`make_celled`]: Self::make_celled
[`make_shared`]: Self::make_shared
[`make_frozen`]: Self::make_frozen
[atomic]: core::sync::atomic::AtomicUsize
[gm]: Self::get_mut
**/
#[repr(transparent)]
pub struct BitRcHandle<R, O = Lsb0, T = usize>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	/// An encoded pointer to the start of the referent [`BitSlice`] region.
	span: BitSpan<Mut, O, T>,
	/// Marks the `Radium` type used to interact with the control counters.
	_rad: PhantomData<R>,
}

impl<R, O, T> BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	/// Views the contained `BitSlice` region.
	#[inline]
	#[cfg(not(tarpaulin_include))]
	pub fn as_bitslice(this: &Self) -> &BitSlice<O, T> {
		this.span.to_bitslice_ref()
	}

	/// Provides a raw pointer to the data.
	///
	/// The counts are not affected in any way and the `BitRcHandle` is not
	/// consumed. The pointer is valid for as long there are strong counts in
	/// the `BitRcHandle`.
	///
	/// # Original
	///
	/// [`Rc::as_ptr`](alloc::rc::Rc::as_ptr)
	///
	/// # API Differences
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::rc::BitRc;
	///
	/// let x = BitRc::from(bits![1, 0, 1, 1, 0]);
	/// let y = BitRc::clone(&x);
	/// let x_ptr = BitRc::as_bitslice_ptr(&x);
	/// assert_eq!(x_ptr, BitRc::as_bitslice_ptr(&y));
	/// assert_eq!(unsafe { &*x_ptr }, &*y);
	/// ```
	#[inline]
	#[cfg(not(tarpaulin_include))]
	pub fn as_bitslice_ptr(this: &Self) -> *const BitSlice<O, T> {
		Self::as_bitslice(this)
	}

	/// Casts the contained `BitSlice` to have the capability for shared
	/// mutation.
	///
	/// This obeys the same uniquity logic as [`Self::make_mut`]: if `this` is
	/// already a unique handle to the region, then the transformation happens
	/// in-place; if there are other handles outstanding, then the region is
	/// copied to a new allocation.
	///
	/// # Parameters
	///
	/// - `this`: A handle to a ref-counted bit-slice.
	///
	/// # Returns
	///
	/// A handle to a ref-counted bit-slice that can support mutation from all
	/// handles.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::rc::BitRc;
	/// use core::cell::Cell;
	///
	/// let rc: BitRc<Lsb0, usize>
	///   = BitRc::from(bits![1, 0, 1, 1, 0]);
	///
	/// let rc2: BitRc<Lsb0, Cell<usize>>
	///   = BitRc::make_shared(rc);
	/// ```
	#[inline]
	pub fn make_shared<A>(mut this: Self) -> BitRcHandle<R, O, A>
	where A: BitStore<Mem = T::Mem> + Radium<Item = T::Mem> {
		if !this.is_unique() {
			this = this.fork();
		}
		this.cast::<A>()
	}

	/// Casts the contained `BitSlice` to no longer have the capability for
	/// shared mutation.
	///
	/// This is the inverse of [`make_shared`]: it removes any aliasing
	/// capability from the `T` parameter, rendering it read-only but safe to
	/// view from multiple threads.
	///
	/// [`make_shared`]: Self::make_shared
	#[inline]
	pub fn make_frozen(mut this: Self) -> BitRcHandle<R, O, T::Mem> {
		if !this.is_unique() {
			this = this.fork();
		}
		this.cast::<T::Mem>()
	}

	/// Converts the refcount to use atomic access.
	///
	/// If `this` is the only pointer to the allocation, then the conversion
	/// happens in-place. If the allocation is shared, then it is copied into a
	/// new allocation.
	///
	/// Note that because this is not specialized, it will clone the allocation
	/// if it shared even if the source handle already uses atomic refcounting.
	///
	/// This does not change the `T: BitStore` parameter! You must *also* use
	/// [`make_shared`] if you wish to cast, for example, `BitRc<_, Cell<u8>>`
	/// into `BitArc<_, AtomicU8>`.
	///
	/// [`make_shared`]: Self::make_shared
	#[inline]
	pub fn make_atomic(this: Self) -> BitArc<O, T> {
		Self::cast_refcount::<RadiumUsize>(this)
	}

	/// Converts the refcount to use non-atomic access.
	///
	/// If `this` is the only pointer to the allocation, then the conversion
	/// happens in-place. If the allocation is shared, then it is copied into a
	/// new allocation.
	///
	/// Note that because this is not specialized, it will clone the allocation
	/// if it shared even if the source handle already uses non-atomic
	/// refcounting.
	///
	/// This does not change the `T: BitStore` parameter! You must *also* use
	/// [`make_frozen`] if you wish to cast, for example,
	/// `BitArc<_, AtomicU8>` into `BitRc<_, Cell<u8>>`.
	///
	/// [`make_frozen`]: Self::make_frozen
	#[inline]
	pub fn make_celled(this: Self) -> BitRc<O, T> {
		Self::cast_refcount::<Cell<usize>>(this)
	}

	/// Allocates a new `BitRcHandle` from a provided `BitSpan` descriptor.
	fn new_from_bitspan(src: BitSpan<Const, O, T>) -> Self {
		let (_, head, bits) = src.raw_parts();
		let mut buf =
			vec![0usize; 1 + elts::<usize>(bits + head.into_inner() as usize)];
		buf[0] = 1;
		let mut buf = buf.into_boxed_slice().pipe(ManuallyDrop::new);
		let span = BitSpan::new(
			unsafe { buf.as_mut_ptr().add(1).force_wrap() }.cast::<T>(),
			head,
			bits,
		)
		.unwrap();
		span.to_bitslice_mut()
			.copy_from_bitslice(src.to_bitslice_ref());
		Self {
			span,
			_rad: PhantomData,
		}
	}

	/// Unconditionally forks the contained `BitSlice` into a new allocation,
	/// rather than only incrementing the reference counter as in `Clone`.
	fn fork(&self) -> Self {
		Self::from(&**self)
	}

	/// Casts the `BitSlice` to have a new datatype.
	fn cast<U>(self) -> BitRcHandle<R, O, U>
	where U: BitStore {
		BitRcHandle {
			span: self.pipe(ManuallyDrop::new).span.cast::<U>(),
			_rad: PhantomData,
		}
	}

	/// Casts the refcount type. This forks the allocation if it is not uniquely
	/// held.
	#[inline]
	fn cast_refcount<R2>(mut this: Self) -> BitRcHandle<R2, O, T>
	where R2: Radium<Item = usize> {
		if !this.is_unique() {
			this = this.fork();
		}
		BitRcHandle {
			span: ManuallyDrop::new(this).span,
			_rad: PhantomData,
		}
	}

	/// Tests if a `BitRcHandle` is the sole known reference to a region.
	///
	/// Untracked pointers, such as produced by [`Self::into_raw`], are on
	/// their own.
	#[inline]
	fn is_unique(&self) -> bool {
		Self::strong_count(self) == 1
	}

	/// Increments the refcount, returning the previous count.
	fn incr(&self) -> usize {
		self.refcount_slot().fetch_add(1, Ordering::SeqCst)
	}

	/// Decrements the refcount, returning the previous count.
	fn decr(&self) -> usize {
		self.refcount_slot().fetch_sub(1, Ordering::SeqCst)
	}

	/// Acquires a reference to the refcount slot.
	fn refcount_slot(&self) -> &R {
		unsafe { &*self.span.address().to_const().cast::<R>().sub(1) }
	}

	/// Acquires a pointer to the entire allocated buffer.
	fn buf(&self) -> NonNull<[usize]> {
		ptr::slice_from_raw_parts_mut(
			(self.refcount_slot() as *const R as *mut R).cast::<usize>(),
			crate::mem::elts::<usize>(self.span.len()) + 1,
		)
		.pipe(|ptr| unsafe { NonNull::new_unchecked(ptr) })
	}
}

#[cfg(test)]
mod tests;
