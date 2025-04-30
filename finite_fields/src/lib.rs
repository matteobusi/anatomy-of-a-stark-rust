#![feature(adt_const_params)]
#![feature(structural_match)]
#![allow(incomplete_features)]

#![warn(missing_docs)]
//! This crate is a proof-of-concept and it has not been audited nor formally verified (yet!)
//! Also, we use big ints from a slightly modified crypto-bigint that allows using constant non-native types
//! as generics parameters, which allow a lot of constant usage.
//! This may change in the future!

use crypto_bigint::{NonZero, I256, U256};

/// This module provides basic operations over finite fields, and in particular over Z/p
pub mod field_element;

/// This is the prime number we'll base our system on
const P : NonZero<U256> = NonZero::<U256>::new_unwrap(U256::from_u128(0xcb800000000000000000000000000001));

/// This is the corresponding generator
const G : NonZero<U256> = NonZero::<U256>::new_unwrap(U256::from_u128(0x4040fbed12ee470fb5038f9c18f6f7d1));

/// The type corresponding to the field we are going to use in our proof-of-concept
pub type IntPG = field_element::IntMod<P, G>;

/// The ZERO element of the finite field `IntPG`
pub const ZERO : IntPG = IntPG { val : I256::ZERO };

/// The ONE element of the finite field `IntPG`
pub const ONE : IntPG = IntPG { val : I256::ONE };

/// Lifts a I256 value into IntPG
pub fn constant (c : I256) -> IntPG {
    IntPG { val : (c % P) }
}

/// A function to pseudo-randomly sample from the field, given a random `seed`
pub fn sample <const P : NonZero<U256>, const G : NonZero<U256>> (seed : &[u8]) -> field_element::IntMod<P, G> {
    let mut acc : I256 = I256::ZERO;
    for b in seed {
        acc = (acc << 8) ^ I256::from(*b as i8);
    }

    field_element::IntMod { val : acc % P }
}
