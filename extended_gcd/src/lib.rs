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
    if b == I512::ZERO {
        ExtendedGCDResult {
            x : I512::ONE,
            y : I512::ZERO,
            g : a
        }
    } else {
        let nzb = NonZero::new(b).expect("Never happens!");
        let ExtendedGCDResult {x, y, g} = extended_gcd(b, a % nzb);

        ExtendedGCDResult {
            x : y,
            y : x - (a / nzb).expect("Never happens!") * y,
            g
        }
    }
}
