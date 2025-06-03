use core::fmt;
use std::ops::*;
use crypto_bigint::{ConstChoice, NonZero, I256, U512, U256};

use extended_gcd::{ExtendedGCDResult, extended_gcd};
use serde::{de::Visitor, ser::SerializeSeq, Deserialize, Serialize};

/// Finite field element, with value `val` and belonging to the finite field `ff`
#[derive(Clone, PartialOrd, Ord, Copy, PartialEq, Eq, Hash)]
pub struct IntMod <const P : NonZero<U256>, const G : NonZero<U256>> {
    /// `val` denotes the value of the integer modulo `P`
    val : U256
}

// The implementation for PartialEq and Eq should be the following, but by careful use of private val we can avoid fiddling with PartialEq default implementation
// impl<const P : NonZero<U256>, const G : NonZero<U256>> PartialEq for IntMod<P, G> {
//     fn eq(&self, other: &Self) -> bool {
//         (self.val % P) == (other.val % P)
//     }
// }

// impl<const P : NonZero<U256>, const G : NonZero<U256>> Eq for IntMod<P, G> { }


impl<const P : NonZero<U256>, const G : NonZero<U256>> IntMod<P, G> {
    /// Lifts a I256 value into `IntMod<P, G>`
    pub fn constant (c : &U256) -> Self {
        Self { val : c%P }
    }

    /// The ZERO element of the finite field `IntMod<P, G>`
    pub const ZERO : Self = Self { val: U256::ZERO };

    /// The ONE element of the finite field `IntMod<P, G>`
    pub const ONE : Self = Self { val: U256::ONE };
}


impl<const P : NonZero<U256>, const G : NonZero<U256>> Serialize for IntMod<P, G> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer {
            let words = self.val.to_words();
            let mut seq = serializer.serialize_seq(Some(4))?;
            seq.serialize_element(&words[0])?;
            seq.serialize_element(&words[1])?;
            seq.serialize_element(&words[2])?;
            seq.serialize_element(&words[3])?;
            seq.end()
    }
}

impl<'de, const P : NonZero<U256>, const G : NonZero<U256>> Deserialize<'de> for IntMod<P, G> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de> {
            struct U64SeqVisitor;

            impl<'de> Visitor<'de> for U64SeqVisitor {
                type Value = [u64; 4];

                fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                    formatter.write_str(stringify!(u64))
                }

                fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
                    where
                        A: serde::de::SeqAccess<'de>, {

                        let mut res = Vec::new();
                        while let Some (v) = seq.next_element()? {
                            res.push(v)
                        }

                        assert_eq! (res.len(), 4);

                        // Sorry :)
                        Ok([res[0], res[1], res[2], res[3]])
                }
            }

            Ok(IntMod::constant(&U256::from_words(deserializer.deserialize_seq(U64SeqVisitor)?)))

    }
}


/// ZpElement is a FiniteFieldElement and implements the `Add` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> Add for IntMod<P, G> {
    type Output = Self;

    fn add (self, rhs : Self) -> Self {
        // This is not the most efficient way, but it is the easiest
        // Notice that the widening is just internal, thanks to the modulus
        let self_u512 : U512 = self.val.widening_mul(&U256::ONE);
        let rhs_u512 : U512 = rhs.val.widening_mul(&U256::ONE);

        #[allow(non_snake_case)]
        let P_U512 : NonZero<U512> = NonZero::new(P.widening_mul(&U256::ONE)).unwrap();

        // We need to make sure this fits in 512 bits
        let res_u512 = (self_u512 + rhs_u512)%P_U512;

        let res_u512_limbs = res_u512.to_limbs();
        let res : U256 = U256::new([
            res_u512_limbs[0], res_u512_limbs[1], res_u512_limbs[2], res_u512_limbs[3]
        ]);

        IntMod::constant(&res)
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
        IntMod::constant(&(P.get() + self.val - rhs.val))
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
        let P_U512 : NonZero<U512> = NonZero::new(P.get().widening_mul(&U256::ONE)).unwrap();

        #[allow(clippy::suspicious_arithmetic_impl)]
        let res_u512 = (self.val.widening_mul(&rhs.val) % P_U512).to_limbs();
        let res : U256 = U256::new([
            res_u512[0], res_u512[1], res_u512[2], res_u512[3]
        ]);

        IntMod::constant(&res)
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
        if denominator.val == U256::ZERO {
            panic!("Zero is an invalid denominator!");
        }

        let signed_den = I256::new_from_abs_sign(denominator.val, ConstChoice::FALSE).unwrap();
        #[allow(non_snake_case)]
        let signed_P = I256::new_from_abs_sign(P.get(), ConstChoice::FALSE).unwrap();

        let ExtendedGCDResult { x, y: _, g: _ } = extended_gcd(signed_den, signed_P);

        let x = x.normalized_rem(&P);
        // dbg!(denominator.val);
        // dbg!(P.get());
        // dbg!(self.val);
        // dbg!(x);
        // dbg!(self.val * x);
        // dbg!((self.val * x) % P);
        // assert!(false);

        IntMod::constant(&(self.val * x))
    }
}

/// ZpElement is a FiniteFieldElement and implements the `DivAssign` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> DivAssign for IntMod<P, G> {
    fn div_assign(&mut self, denominator: Self) {
        *self = *self / denominator;
    }
}


/// ZpElement is a FiniteFieldElement and implements the `Shr` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> Shr<u32> for IntMod<P, G> {
    type Output = Self;

    fn shr(self, rhs: u32) -> Self {
        Self { val: (self.val >> rhs) % P }
    }
}

/// ZpElement is a FiniteFieldElement and implements the `ShrAssign` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> ShrAssign<u32> for IntMod<P, G> {
    fn shr_assign(&mut self, rhs: u32) {
        *self = *self >> rhs;
    }
}

/// ZpElement is a FiniteFieldElement and implements the `Rem` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> Rem for IntMod<P, G> {
    type Output = Self;

    fn rem (self, denominator : IntMod<P, G>) -> Self {
        IntMod {
            val: (self.val - denominator.val * (self.val / NonZero::new(denominator.val).unwrap())) % P
        }
    }
}

/// ZpElement is a FiniteFieldElement and implements the `BitXor` trait
impl<const P : NonZero<U256>, const G : NonZero<U256>> BitXor for IntMod<P, G> {
    type Output = Self;

    fn bitxor (self, exp : Self) -> Self {
        #[allow(non_snake_case)]
        let P_U512 : NonZero<U512> = NonZero::new(P.get().widening_mul(&U256::ONE)).unwrap();

        let mut res = U256::ONE;
        let mut _a = self.val;
        let mut _b = exp.val;

        while _b > U256::ZERO {
            if _b & U256::ONE == U256::ONE {
                #[allow(clippy::suspicious_arithmetic_impl)]
                let res_u512 = (res.widening_mul(&_a) % P_U512).to_limbs();

                res = U256::new([
                    res_u512[0], res_u512[1], res_u512[2], res_u512[3]
                ]);
            }

            let _a_u512 = (_a.widening_mul(&_a) % P_U512).to_limbs();
            _a = U256::new([
                _a_u512[0], _a_u512[1], _a_u512[2], _a_u512[3]
            ]);
            _b >>= 1
        }

        IntMod { val: res%P }
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
            val: (P.get() - self.val) % P,
        }
    }
}

/// ZpElement is a FiniteFieldElement
impl<const P : NonZero<U256>, const G : NonZero<U256>> IntMod<P, G> {
    /// Returns the value in the finite field
    pub fn inverse (&self) -> Self {
        let signed_self = I256::new_from_abs_sign(self.val, ConstChoice::FALSE).unwrap();
        #[allow(non_snake_case)]
        let signed_P = I256::new_from_abs_sign(P.get(), ConstChoice::FALSE).unwrap();

        let ExtendedGCDResult { x, y: _, g: _ } = extended_gcd(signed_self, signed_P);

        let x = x.normalized_rem(&P);
        IntMod { val: (x + P.get()) % P }
    }
}

/// Create a ZpElement from an u8
impl<const P : NonZero<U256>, const G : NonZero<U256>> From<u8> for IntMod<P, G> {
    fn from(value: u8) -> Self {
        IntMod::constant(&U256::from(value))
    }
}

/// Create a ZpElement from an u16
impl<const P : NonZero<U256>, const G : NonZero<U256>> From<u16> for IntMod<P, G> {
    fn from(value: u16) -> Self {
        IntMod::constant(&U256::from(value))
    }
}

/// Create a ZpElement from an u32
impl<const P : NonZero<U256>, const G : NonZero<U256>> From<u32> for IntMod<P, G> {
    fn from(value: u32) -> Self {
        IntMod::constant(&U256::from(value))
    }
}

/// Create a ZpElement from an u64
impl<const P : NonZero<U256>, const G : NonZero<U256>> From<u64> for IntMod<P, G> {
    fn from(value: u64) -> Self {
        IntMod::constant(&U256::from(value))
    }
}

/// Create a ZpElement from an u128
impl<const P : NonZero<U256>, const G : NonZero<U256>> From<u128> for IntMod<P, G> {
    fn from(value: u128) -> Self {
        IntMod::constant(&U256::from(value))
    }
}

/// Create a ZpElement from an usize
impl<const P : NonZero<U256>, const G : NonZero<U256>> From<usize> for IntMod<P, G> {
    fn from(value: usize) -> Self {
        IntMod { val: U256::from_u128(value as u128)%P } // This should suffice in avoiding overflows with conversion from unsigned to signed

    }
}

/// Create a ZpElement from an i32
impl<const P : NonZero<U256>, const G : NonZero<U256>> From<i16> for IntMod<P, G> {
    fn from(value: i16) -> Self {
        assert! (value >= 0);

        IntMod { val: U256::from_u16(value as u16)%P }
    }
}
/// Create a ZpElement from an i32
impl<const P : NonZero<U256>, const G : NonZero<U256>> From<i32> for IntMod<P, G> {
    fn from(value: i32) -> Self {
        assert! (value >= 0);

        IntMod { val: U256::from_u32(value as u32)%P }

    }
}

/// Create a ZpElement from an i64
impl<const P : NonZero<U256>, const G : NonZero<U256>> From<i64> for IntMod<P, G> {
    fn from(value: i64) -> Self {
        assert! (value >= 0);

        IntMod { val: U256::from_u64(value as u64)%P }

    }
}

/// Create a ZpElement from an i128
impl<const P : NonZero<U256>, const G : NonZero<U256>> From<i128> for IntMod<P, G> {
    fn from(value: i128) -> Self {
        assert! (value >= 0);

        IntMod { val: U256::from_u128(value as u128)%P }

    }
}

impl<const P : NonZero<U256>, const G : NonZero<U256>> fmt::Debug for IntMod<P, G> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Contrary to the library we want the sign ...
        // if self.val.is_negative().into() {
        //     let p_value : U256 = self.val * U256::from(-1);
        //     write!(f, "- {}", p_value)
        // } else {
            write!(f, "{}", self.val)
        // }
    }
}


#[cfg(test)]
mod tests {
    use crate::IntPG;

    use crypto_bigint::U256;

    #[test]
    fn test_add () {
        let a = IntPG::constant(&U256::from_be_hex("0000000000000000000000000000000064C67A557940A1A6BF5F894F3B5B4AF4"));

        let b = IntPG::constant(&U256::from_be_hex("000000000000000000000000000000007655E0F19802F30E2915BBD5F9018C3D"));

        let expected = IntPG::constant(&U256::from_be_hex("000000000000000000000000000000000f9c5b47114394b4e8754525345cd730"));

        assert_eq!(a+b, expected);
    }

    #[test]
    fn test_mul () {
        let a = IntPG::constant(&U256::from_be_hex("0000000000000000000000000000000064C67A557940A1A6BF5F894F3B5B4AF4"));

        let b = IntPG::constant(&U256::from_be_hex("000000000000000000000000000000007655E0F19802F30E2915BBD5F9018C3D"));

        let expected = IntPG::constant(&U256::from_be_hex("00000000000000000000000000000000c8842392a57b018f4ecfeadf09df1511"));

        assert_eq!(a*b, expected);
    }

    #[test]
    fn test_div () {
        let a = IntPG::constant(&U256::from_be_hex("00000000000000000000000000000000a50c3796936d5035181e4468f1f81083"));

        let b = IntPG::constant(&U256::from_be_hex("000000000000000000000000000000004040fbed12ee470fb5038f9c18f6f7d1"));

        let expected = IntPG::constant(&U256::from_be_hex("00000000000000000000000000000000508e83dc0a0b78912521d2d5026d0bda"));

        assert_eq!(a/b, expected);
    }

    #[test]
    fn test_rem_even () {
        let even = IntPG::from(42u32);

        assert_eq!(even % IntPG::from(2u32), IntPG::ZERO);
    }
    #[test]
    fn test_rem_odd () {
        let odd = IntPG::from(29u32);

        assert_eq!(odd % IntPG::from(2u32), IntPG::ONE);
    }

    #[test]
    fn test_serde () {
        let value = IntPG::from (120u32);

        let serialized = serde_json::to_string(&value).unwrap();
        let deserialized: IntPG = serde_json::from_str(&serialized).unwrap();

        assert_eq!(value, deserialized);
    }
}
