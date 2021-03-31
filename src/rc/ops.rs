use alloc::boxed::Box;
use core::ops::{
	BitAnd,
	BitAndAssign,
	BitOr,
	BitOrAssign,
	BitXor,
	BitXorAssign,
	Deref,
};

use radium::Radium;

use super::BitRcHandle;
use crate::{
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
};

#[cfg(not(tarpaulin_include))]
impl<R, O, T, Rhs> BitAnd<Rhs> for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T>: BitAndAssign<Rhs>,
{
	type Output = Self;

	#[inline]
	fn bitand(mut self, rhs: Rhs) -> Self::Output {
		self &= rhs;
		self
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O, T, Rhs> BitAndAssign<Rhs> for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T>: BitAndAssign<Rhs>,
{
	#[inline]
	fn bitand_assign(&mut self, rhs: Rhs) {
		*Self::make_mut(self) &= rhs;
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O, T, Rhs> BitOr<Rhs> for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T>: BitOrAssign<Rhs>,
{
	type Output = Self;

	#[inline]
	fn bitor(mut self, rhs: Rhs) -> Self::Output {
		self |= rhs;
		self
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O, T, Rhs> BitOrAssign<Rhs> for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T>: BitOrAssign<Rhs>,
{
	#[inline]
	fn bitor_assign(&mut self, rhs: Rhs) {
		*Self::make_mut(self) |= rhs;
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O, T, Rhs> BitXor<Rhs> for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T>: BitXorAssign<Rhs>,
{
	type Output = Self;

	#[inline]
	fn bitxor(mut self, rhs: Rhs) -> Self::Output {
		self ^= rhs;
		self
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O, T, Rhs> BitXorAssign<Rhs> for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T>: BitXorAssign<Rhs>,
{
	#[inline]
	fn bitxor_assign(&mut self, rhs: Rhs) {
		*Self::make_mut(self) ^= rhs;
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O, T> Deref for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	type Target = BitSlice<O, T>;

	#[inline]
	fn deref(&self) -> &Self::Target {
		Self::as_bitslice(self)
	}
}

impl<R, O, T> Drop for BitRcHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	/// Drops the `BitRcHandle`.
	///
	/// This will decrement the reference count. If the reference count reaches
	/// zero then we drop the inner `BitSlice`.
	///
	/// # Original
	///
	/// [`<Rc as Drop>::drop`](alloc::rc::Rc::drop)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::rc::BitRc;
	///
	/// let rc = BitRc::from(bits![0, 1, 1, 0, 1]);
	/// let rc2 = BitRc::clone(&rc);
	///
	/// assert_eq!(BitRc::strong_count(&rc2), 2);
	/// drop(rc);
	/// assert_eq!(BitRc::strong_count(&rc2), 1);
	/// drop(rc2);
	/// // deällocated here.
	/// ```
	#[inline]
	fn drop(&mut self) {
		if self.decr() == 1 {
			drop(unsafe { Box::from_raw(self.buf().as_ptr()) });
		}
	}
}
