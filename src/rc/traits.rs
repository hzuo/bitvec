use alloc::{
	borrow::Cow,
	rc::Rc,
};
use core::{
	borrow::Borrow,
	cmp,
	convert::{
		TryFrom,
		TryInto,
	},
	fmt::{
		self,
		Binary,
		Debug,
		Display,
		Formatter,
		LowerHex,
		Octal,
		UpperHex,
	},
	hash::{
		Hash,
		Hasher,
	},
	iter::FromIterator,
};

use radium::Radium;

use super::BitRcHandle;
use crate::{
	array::BitArray,
	boxed::BitBox,
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
	vec::BitVec,
};

#[cfg(not(tarpaulin_include))]
impl<R, O, T> Borrow<BitSlice<O, T>> for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn borrow(&self) -> &BitSlice<O, T> {
		Self::as_bitslice(self)
	}
}

impl<R, O, T> Clone for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	/// Makes a clone of the `BitRcHandle` pointer.
	///
	/// This creates another pointer to the same allocation, increasing the
	/// reference count.
	///
	/// # Original
	///
	/// [`<Rc as Clone>::clone`](alloc::rc::Rc::clone)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::rc::BitRc;
	///
	/// let rc = BitRc::from(bits![1, 0, 1, 1, 0]);
	/// let rc2 = BitRc::clone(&rc);
	/// ```
	#[inline]
	fn clone(&self) -> Self {
		self.incr();
		Self { ..*self }
	}
}

impl<R, O, T> Eq for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
}

#[cfg(not(tarpaulin_include))]
impl<R, O, T> Ord for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn cmp(&self, other: &Self) -> cmp::Ordering {
		Self::as_bitslice(self).cmp(Self::as_bitslice(other))
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O1, O2, T1, T2> PartialEq<BitRcHandle<R, O2, T2>> for BitSlice<O1, T1>
where
	R: Radium<Item = usize>,
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn eq(&self, other: &BitRcHandle<R, O2, T2>) -> bool {
		self == BitRcHandle::as_bitslice(other)
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O1, O2, T1, T2> PartialEq<BitRcHandle<R, O2, T2>> for &BitSlice<O1, T1>
where
	R: Radium<Item = usize>,
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn eq(&self, other: &BitRcHandle<R, O2, T2>) -> bool {
		*self == BitRcHandle::as_bitslice(other)
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O1, O2, T1, T2> PartialEq<BitRcHandle<R, O2, T2>>
	for &mut BitSlice<O1, T1>
where
	R: Radium<Item = usize>,
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn eq(&self, other: &BitRcHandle<R, O2, T2>) -> bool {
		**self == BitRcHandle::as_bitslice(other)
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O, T, Rhs> PartialEq<Rhs> for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
	Rhs: ?Sized + PartialEq<BitSlice<O, T>>,
{
	#[inline]
	fn eq(&self, other: &Rhs) -> bool {
		other == Self::as_bitslice(self)
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O1, O2, T1, T2> PartialOrd<BitRcHandle<R, O2, T2>> for BitSlice<O1, T1>
where
	R: Radium<Item = usize>,
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn partial_cmp(
		&self,
		other: &BitRcHandle<R, O2, T2>,
	) -> Option<cmp::Ordering> {
		self.partial_cmp(BitRcHandle::as_bitslice(other))
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O, T, Rhs> PartialOrd<Rhs> for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
	Rhs: ?Sized + PartialOrd<BitSlice<O, T>>,
{
	#[inline]
	fn partial_cmp(&self, other: &Rhs) -> Option<cmp::Ordering> {
		other.partial_cmp(Self::as_bitslice(self))
	}
}

#[cfg(not(tarpaulin_include))]
impl<'a, R, O1, O2, T1, T2> PartialOrd<BitRcHandle<R, O2, T2>>
	for &'a BitSlice<O1, T1>
where
	R: Radium<Item = usize>,
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn partial_cmp(
		&self,
		other: &BitRcHandle<R, O2, T2>,
	) -> Option<cmp::Ordering> {
		self.partial_cmp(BitRcHandle::as_bitslice(other))
	}
}

#[cfg(not(tarpaulin_include))]
impl<'a, R, O1, O2, T1, T2> PartialOrd<BitRcHandle<R, O2, T2>>
	for &'a mut BitSlice<O1, T1>
where
	R: Radium<Item = usize>,
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn partial_cmp(
		&self,
		other: &BitRcHandle<R, O2, T2>,
	) -> Option<cmp::Ordering> {
		self.partial_cmp(BitRcHandle::as_bitslice(other))
	}
}

impl<R, O, T> AsRef<BitSlice<O, T>> for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn as_ref(&self) -> &BitSlice<O, T> {
		Self::as_bitslice(self)
	}
}

impl<R, O, T> From<&BitSlice<O, T>> for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn from(bitslice: &BitSlice<O, T>) -> Self {
		Self::new_from_bitspan(bitslice.as_bitspan())
	}
}

impl<R, O, T> From<BitArray<O, T>> for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn from(bv: BitArray<O, T>) -> Self {
		Self::new_from_bitspan(bv.as_bitslice().as_bitspan())
	}
}

impl<R, O, T> From<BitBox<O, T>> for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn from(bv: BitBox<O, T>) -> Self {
		Self::new_from_bitspan(bv.as_bitslice().as_bitspan())
	}
}

impl<R, O, T> From<BitVec<O, T>> for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn from(bv: BitVec<O, T>) -> Self {
		Self::new_from_bitspan(bv.as_bitslice().as_bitspan())
	}
}

impl<R, O, T> From<Cow<'_, BitSlice<O, T>>> for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn from(cow: Cow<'_, BitSlice<O, T>>) -> Self {
		Self::from(cow.borrow())
	}
}

impl<R, O, T, const N: usize> TryFrom<BitRcHandle<R, O, T>>
	for Rc<BitArray<O, [T; N]>>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	type Error = BitRcHandle<R, O, T>;

	fn try_from(this: BitRcHandle<R, O, T>) -> Result<Self, Self::Error> {
		match BitRcHandle::as_bitslice(&this).try_into() {
			Ok(bitarr) => Ok(Rc::new(bitarr)),
			Err(_) => Err(this),
		}
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O, T> Default for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn default() -> Self {
		Self::new(BitArray::new([]))
	}
}

impl<R, O, T> Binary for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Binary::fmt(Self::as_bitslice(self), fmt)
	}
}

impl<R, O, T> Debug for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Debug::fmt(Self::as_bitslice(self), fmt)
	}
}

impl<R, O, T> Display for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Display::fmt(Self::as_bitslice(self), fmt)
	}
}

impl<R, O, T> LowerHex for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		LowerHex::fmt(Self::as_bitslice(self), fmt)
	}
}

impl<R, O, T> Octal for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Octal::fmt(Self::as_bitslice(self), fmt)
	}
}

impl<R, O, T> UpperHex for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		UpperHex::fmt(Self::as_bitslice(self), fmt)
	}
}

impl<R, O, T> Hash for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn hash<H>(&self, hasher: &mut H)
	where H: Hasher {
		Self::as_bitslice(self).hash(hasher)
	}
}

impl<R, O, T, Item> FromIterator<Item> for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
	BitVec<O, T>: FromIterator<Item>,
{
	/// Takes each element in the ``Iterator and collects it into a
	/// `BitRcHandle`.
	///
	/// The source iterator must be collectible into a [`BitVec`]. This can be
	/// `bool`s, `&bool`s, or `BitRef`s.
	///
	/// Because specialization is unstable, this cannot use the standard library
	/// acceleration, and must always collect into a `BitVec` then convert the
	/// `BitVec` into a `BitRcHandle`.
	///
	/// # Original
	///
	/// [`<Rc as FromIterator>::from_iter`](alloc::rc::Rc::from_iter)
	///
	/// [`BitVec`]: crate::vec::BitVec
	#[inline]
	fn from_iter<IntoIter>(iter: IntoIter) -> Self
	where IntoIter: IntoIterator<Item = Item> {
		Self::from(BitVec::from_iter(iter))
	}
}

unsafe impl<R, O, T> Send for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize> + Sync,
	O: BitOrder,
	T: BitStore + Sync,
{
}

unsafe impl<R, O, T> Sync for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize> + Sync,
	O: BitOrder,
	T: BitStore + Sync,
{
}

impl<R, O, T> Unpin for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
}
