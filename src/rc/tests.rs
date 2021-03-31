#![cfg(test)]

use core::pin::Pin;

use radium::types::RadiumUsize;

use super::*;
use crate::prelude::*;

#[test]
fn usage() {
	let pinned = BitRc::pin(BitArray::<Msb0, _>::new([0xA5u8, 0x96u8]));
	let rc = Pin::into_inner(pinned);
	assert_eq!(rc.len(), 16);
	assert_eq!(BitRc::strong_count(&rc), 1);

	let rc2 = BitRc::clone(&rc);
	assert_eq!(BitRc::strong_count(&rc2), 2);

	assert_eq!(BitRc::strong_count(&rc), 2);
	assert!(BitRc::try_unwrap(rc2).is_err());
	assert_eq!(BitRc::strong_count(&rc), 1);
	let boxed = BitRc::try_unwrap(rc).unwrap();

	let rc = BitRc::from(&boxed[2 .. 14]);
	assert_eq!(rc.len(), 12);

	let ptr = BitRc::into_raw(rc);
	let rc = unsafe {
		let rc = BitRc::from_raw(ptr);
		assert_eq!(BitRc::strong_count(&rc), 1);
		BitRc::increment_strong_count(ptr);
		assert_eq!(BitRc::strong_count(&rc), 2);
		BitRc::decrement_strong_count(ptr);
		assert_eq!(BitRc::strong_count(&rc), 1);
		rc
	};

	let mut rc2 = rc.clone();
	assert!(BitRc::get_mut(&mut rc2).is_none());
	assert!(BitRc::ptr_eq(&rc, &rc2));

	let _ = BitRc::make_mut(&mut rc2);
	assert!(!BitRc::ptr_eq(&rc, &rc2));
}

#[test]
fn casting() {
	let rc: BitRc<Lsb0, usize> = BitRc::from(bits![1, 0, 1, 1, 0]);
	let rc2 = rc.clone();

	assert!(BitRc::ptr_eq(&rc, &rc2));

	let rc3: BitRc<Lsb0, RadiumUsize> = BitRc::make_shared(rc);
	assert!(!BitRc::ptr_eq(&rc2, &rc3));

	let rc3_ptr = BitRc::as_bitslice_ptr(&rc3);
	assert!(rc3.is_unique());
	let rc4: BitRc<Lsb0, usize> = BitRc::make_frozen(rc3);
	let rc4_ptr = BitRc::as_bitslice_ptr(&rc4);
	assert_eq!(rc3_ptr as *const BitSlice<Lsb0, usize>, rc4_ptr);

	let rc5: BitArc<Lsb0, usize> = BitRc::make_atomic(rc2);
	let rc5_ptr = BitArc::as_bitslice_ptr(&rc5);
	let rc6: BitRc<Lsb0, Cell<usize>> =
		BitRc::make_shared(BitArc::make_celled(rc5));
	let rc6_ptr = BitRc::as_bitslice_ptr(&rc6);
	assert_eq!(rc5_ptr as *const BitSlice, rc6_ptr as *const BitSlice);
}
