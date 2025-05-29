#![feature(adt_const_params)]
#![feature(structural_match)]
#![allow(incomplete_features)]

#![warn(missing_docs)]
//! This crate is a proof-of-concept and it has not been audited nor formally verified (yet!)
//! Also, we use big ints from a slightly modified crypto-bigint that allows using constant non-native types
//! as generics parameters, which allow a lot of constant usage.
//! This may change in the future!
use crypto_bigint::{NonZero, I512, U512};

/// This module provides basic operations over finite fields, and in particular over Z/p
pub mod field_element;

/// This is the prime number we'll base our system on
pub const P : NonZero<U512> = NonZero::<U512>::new_unwrap(U512::from_u128(0xcb800000000000000000000000000001));

/// This is the corresponding generator
pub const G : NonZero<U512> = NonZero::<U512>::new_unwrap(U512::from_u128(0x4040fbed12ee470fb5038f9c18f6f7d1));
/// This is the signed version of the generator, for easier use
pub const SIGNED_G : I512 = I512::from_i128(0x4040fbed12ee470fb5038f9c18f6f7d1);

/// The type corresponding to the field we are going to use in our proof-of-concept
pub type IntPG = field_element::IntMod<P, G>;

/// A function that returns the primitive nth root of the field with parameters P and G (fixed)
pub fn primitive_nth_root (n : i32) -> IntPG {
    assert! (I512::from(n) <= I512::ONE.shl(119) && (n & (n - 1)) == 0);

    let mut root = IntPG::constant(&SIGNED_G);
    let mut order = I512::ONE.shl(119);

    while order != n.into() {
        root ^= 2.into();
        order /= NonZero::<U512>::new_unwrap(U512::from_u32(2));
    }

    root
}

/// A function to pseudo-randomly sample from the field, given a random `seed`
pub fn sample <const P : NonZero<U512>, const G : NonZero<U512>> (seed : &[u8]) -> field_element::IntMod<P, G> {
    let mut acc : I512 = I512::ZERO;
    for b in seed {
        acc = (acc << 8) ^ I512::from(*b as i8);
    }

    field_element::IntMod::constant(&acc)
}
