use std::ops::*;
use crypto_bigint::{NonZero, I256, I512, U256};

use extended_gcd::{ExtendedGCDResult, extended_gcd};

/// Finite field element, with value `val` and belonging to the finite field `ff`
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Copy, Hash)]
pub struct IntMod <const P : NonZero<U256>, const G : NonZero<U256>> {
    /// `val` denotes the value of the integer modulo `P`
    pub val : I256
}

/// ZpElement is a FiniteFieldElement and implements the `Add` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> Add for IntMod<P, G> {
    type Output = Self;

    fn add (self, rhs : Self) -> Self {
        // This is not the most efficient way, but it is the easiest
        // Notice that the widening is just internal, thanks to the modulus
        let self_i512 : I512 = self.val.widening_mul(&I256::ONE);
        let rhs_i512 : I512 = rhs.val.widening_mul(&I256::ONE);
        #[allow(non_snake_case)]
        let P_i512 : NonZero<I512> = NonZero::new(P.as_int().widening_mul(&I256::ONE)).unwrap();

        let res_i512 = ((self_i512 + rhs_i512) % P_i512).to_limbs();
        let res : I256 = I256::new([ res_i512[0], res_i512[1], res_i512[2], res_i512[3] ]);

        IntMod {
            val : res
        }
    }
}

/// ZpElement is a FiniteFieldElement and implements the `AddAssign` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> AddAssign for IntMod<P, G> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

/// ZpElement is a FiniteFieldElement and implements the `Sub` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> Sub for IntMod<P, G> {
    type Output = Self;

    fn sub (self, rhs : Self) -> Self {
        IntMod {
            val : (P.as_int() + self.val - rhs.val) % P,
        }
    }
}

/// ZpElement is a FiniteFieldElement and implements the `SubAssign` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> SubAssign for IntMod<P, G> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

/// ZpElement is a FiniteFieldElement and implements the `Mul` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> Mul for IntMod<P, G> {
    type Output = Self;

    fn mul (self, rhs : Self) -> Self {
        // This is not the most efficient way, but it is the easiest
        // Notice that the widening is just internal, thanks to the modulus
        #[allow(non_snake_case)]
        let P_i512 : NonZero<I512> = NonZero::new(P.as_int().widening_mul(&I256::ONE)).unwrap();

        #[allow(clippy::suspicious_arithmetic_impl)]
        let res_i512: [crypto_bigint::Limb; 8] = (self.val.widening_mul(&rhs.val) % P_i512).to_limbs();
        let res : I256 = I256::new([ res_i512[0], res_i512[1], res_i512[2], res_i512[3] ]);

        IntMod {
            val : res
        }
    }
}

/// ZpElement is a FiniteFieldElement and implements the `MulAssign` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> MulAssign for IntMod<P, G> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

/// ZpElement is a FiniteFieldElement and implements the `Div` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> Div for IntMod<P, G> {
    type Output = Self;

    fn div (self, denominator : IntMod<P, G>) -> Self {
        if denominator.val == I256::ZERO {
            panic!("Zero is an invalid denominator!");
        }

        let ExtendedGCDResult { x, y: _, g: _ } = extended_gcd(denominator.val, P.as_int());

        IntMod {
            val : (self.val * x) % P
        }
    }
}

/// ZpElement is a FiniteFieldElement and implements the `DivAssign` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> DivAssign for IntMod<P, G> {
    fn div_assign(&mut self, denominator: Self) {
        *self = *self / denominator;
    }
}

/// ZpElement is a FiniteFieldElement and implements the `Rem` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> Rem for IntMod<P, G> {
    type Output = Self;

    fn rem (self, denominator : IntMod<P, G>) -> Self {
        IntMod {
            val: (self.val - denominator.val * (self.val / NonZero::new(denominator.val).unwrap()).unwrap()) % P
        }
    }
}

/// ZpElement is a FiniteFieldElement and implements the `BitXor` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> BitXor for IntMod<P, G> {
    type Output = Self;

    fn bitxor (self, exp : Self) -> Self {
        let mut res = I256::ONE;
        let mut _a = self.val;
        let mut _b = exp.val;

        while _b > I256::ZERO {
            if _b & I256::ONE == I256::ONE {
                res = (res * _a) % P;
            }
            _a = (_a * _a) % P;
            _b >>= 1
        }

        IntMod { val: res }
    }
}

/// ZpElement is a FiniteFieldElement and implements the `BitXorAssign` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> BitXorAssign for IntMod<P, G> {
    fn bitxor_assign(&mut self, exp: Self) {
        *self = *self ^ exp;
    }
}

/// ZpElement is a FiniteFieldElement and implements the `Neg` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> Neg for IntMod<P, G> {
    type Output = Self;

    fn neg (self) -> Self {
        IntMod {
            val: (P.as_int() - self.val) % P,
        }
    }
}

/// ZpElement is a FiniteFieldElement
impl<const P : NonZero<U256>, const G : NonZero<U256>> IntMod<P, G> {
    /// Returns the value in the finite field
    pub fn inverse (&self) -> Self {
        let ExtendedGCDResult { x, y: _, g: _ } = extended_gcd(self.val, P.as_int());
        IntMod { val: x }
    }
}

/// Create a ZpElement from an i8
impl<const P : NonZero<U256>, const G : NonZero<U256>> From<i8> for IntMod<P, G> {
    fn from(value: i8) -> Self {
        IntMod { val: I256::from(value) }
    }
}

/// Create a ZpElement from an i16
impl<const P : NonZero<U256>, const G : NonZero<U256>> From<i16> for IntMod<P, G> {
    fn from(value: i16) -> Self {
        IntMod { val: I256::from(value) }
    }
}

/// Create a ZpElement from an i32
impl<const P : NonZero<U256>, const G : NonZero<U256>> From<i32> for IntMod<P, G> {
    fn from(value: i32) -> Self {
        IntMod { val: I256::from(value) }
    }
}

/// Create a ZpElement from an i64
impl<const P : NonZero<U256>, const G : NonZero<U256>> From<i64> for IntMod<P, G> {
    fn from(value: i64) -> Self {
        IntMod { val: I256::from(value) }
    }
}

/// Create a ZpElement from an i128
impl<const P : NonZero<U256>, const G : NonZero<U256>> From<i128> for IntMod<P, G> {
    fn from(value: i128) -> Self {
        IntMod { val: I256::from(value) }
    }
}

/// Create a ZpElement from an usize
impl<const P : NonZero<U256>, const G : NonZero<U256>> From<usize> for IntMod<P, G> {
    fn from(value: usize) -> Self {
        IntMod { val: I256::from_i128(value as i128) } // This should suffice in avoiding overflows with conversion from unsigned to signed
    }
}


#[cfg(test)]
mod tests {
    use crate::IntPG;

    use crypto_bigint::I256;

    #[test]
    fn test_rem_even () {
        let even = IntPG::from(42);

        assert_eq!(even % crate::constant(I256::from(2)), crate::ZERO);
    }
    #[test]
    fn test_rem_odd () {
        let odd = IntPG::from(29);

        assert_eq!(odd % crate::constant(I256::from(2)), crate::ONE);
    }
}
