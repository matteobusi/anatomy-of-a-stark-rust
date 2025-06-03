use crypto_bigint::{NonZero, I256};

// x and y are Bezout coefficients and g is the gcd (a, b), this means
// ax + by = g
#[derive(PartialEq, Eq, Debug)]
pub struct ExtendedGCDResult {
    pub x : I256,
    pub y : I256,
    pub g : I256
}

pub fn gcd (a : I256, b : I256) -> I256 {
    if b == I256::ZERO {
        a
    } else {
        gcd (b, a % NonZero::new(b).expect("Never happens!"))
    }
}

pub fn extended_gcd (a : I256, b : I256) -> ExtendedGCDResult {
    let (mut old_r, mut r) = (a, b);
    let (mut old_s, mut s) = (I256::ONE, I256::ZERO);
    let (mut old_t, mut t) = (I256::ZERO, I256::ONE);

    while r != I256::ZERO {
        let quotient : I256 = old_r.checked_div(&r).expect("Never happens!");

        (old_r, r) = (r, old_r - quotient * r);
        (old_s, s) = (s, old_s - quotient * s);
        (old_t, t) = (t, old_t - quotient * t);
    }

    ExtendedGCDResult { x: old_s, y: old_t, g: old_r }
}
