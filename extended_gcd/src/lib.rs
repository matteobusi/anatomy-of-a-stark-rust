use crypto_bigint::{NonZero, I512};

// x and y are Bezout coefficients and g is the gcd (a, b), this means
// ax + by = g
#[derive(PartialEq, Eq, Debug)]
pub struct ExtendedGCDResult {
    pub x : I512,
    pub y : I512,
    pub g : I512
}

pub fn gcd (a : I512, b : I512) -> I512 {
    if b == I512::ZERO {
        a
    } else {
        gcd (b, a % NonZero::new(b).expect("Never happens!"))
    }
}

pub fn extended_gcd (a : I512, b : I512) -> ExtendedGCDResult {
    let (mut old_r, mut r) = (a, b);
    let (mut old_s, mut s) = (I512::ONE, I512::ZERO);
    let (mut old_t, mut t) = (I512::ZERO, I512::ONE);

    while r != I512::ZERO {
        let quotient : I512 = old_r.checked_div(&r).expect("Never happens!");

        (old_r, r) = (r, old_r - quotient * r);
        (old_s, s) = (s, old_s - quotient * s);
        (old_t, t) = (t, old_t - quotient * t);
    }

    ExtendedGCDResult { x: old_s, y: old_t, g: old_r }
}
