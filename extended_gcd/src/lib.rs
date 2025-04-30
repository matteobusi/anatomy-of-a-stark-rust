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
    if b == I256::ZERO {
        ExtendedGCDResult {
            x : I256::ONE,
            y : I256::ZERO,
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
