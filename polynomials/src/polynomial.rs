use std::ops::{Add, BitXor, Div, Mul, Neg, Rem, Sub};

use crypto_bigint::I256;
use finite_fields::IntPG;

use crate::degree::*;

#[derive(Debug, Clone)]
pub struct Polynomial {
    pub coefficients : Vec<IntPG>
}

impl PartialEq for Polynomial {
    fn eq(&self, other: &Self) -> bool {
        (self.is_zero() && other.is_zero()) || self.coefficients == other.coefficients
    }
}

impl Eq for Polynomial { }

impl Neg for Polynomial {
    type Output = Self;

    fn neg (self) -> Polynomial {
        Polynomial { coefficients: self.coefficients.iter().map(|c| - (*c)).collect() }
    }
}

impl Add for Polynomial {
    type Output = Self;

    fn add (self, rhs : Polynomial) -> Polynomial {
        if rhs.clone().degree() == Degree::MinusInf {
            self
        } else if self.degree() == Degree::MinusInf {
            rhs
        } else {
            let mut coefficients = vec![finite_fields::ZERO; self.coefficients.len().max(rhs.coefficients.len())];

            for i in 0..self.coefficients.len() {
                coefficients[i] += self.coefficients[i];
            }

            for i in 0..rhs.coefficients.len() {
                coefficients[i] += rhs.coefficients[i];
            }

            Polynomial { coefficients }
        }
    }
}


impl Sub for Polynomial {
    type Output = Self;

    fn sub (self, rhs : Polynomial) -> Polynomial {
        self.add (-rhs)
    }
}

impl Mul for Polynomial {
    type Output = Self;

    fn mul(self, rhs: Polynomial) -> Polynomial {
        if self.degree() == Degree::MinusInf || rhs.degree() == Degree::MinusInf {
            Polynomial::ZERO
        } else {
            let mut coefficients = vec![finite_fields::ZERO; self.coefficients.len() + rhs.coefficients.len() - 1]; // The -1 is there because the 0th element of the coefficient's vector is the 0-th degree variable

            for i in 0..self.coefficients.len() {
                if self.coefficients[i] == finite_fields::ZERO {
                    continue; // Early exit for 0 coefficients
                }

                for j in 0..rhs.coefficients.len() {
                    coefficients[i+j] += self.coefficients[i] * rhs.coefficients[j]
                }
            }

            Polynomial { coefficients }
        }
    }
}
pub struct DivOutput {
    pub quotient : Polynomial,
    pub remainder : Polynomial
}

impl Div for Polynomial {
    type Output = DivOutput;

    fn div(self, denominator: Polynomial) -> DivOutput {
        match (self.degree(), denominator.degree()) {
            (_, Degree::MinusInf) => panic!("The ZERO polynomial is not a valid denominator!"),
            (Degree::MinusInf, _) => DivOutput { quotient: Polynomial::ZERO, remainder: Polynomial::ZERO },
            (Degree::Poly(n), Degree::Poly(m)) => {
                let mut rem = self.clone();
                let mut quotient_coeff = vec![finite_fields::ZERO; (n - m + 1) as usize];

                while rem.degree() >= Degree::Poly(m) {
                    let coeff = rem.leading_coefficient() / denominator.leading_coefficient();
                    let shift = (rem.degree() - Degree::Poly(m)).unwrap();
                    let mut sub_coefficients = vec![finite_fields::ZERO; shift as usize];
                    sub_coefficients.push(coeff);
                    quotient_coeff[shift as usize] = coeff;
                    let sub = (Polynomial { coefficients: sub_coefficients }) * denominator.clone();

                    rem = rem - sub;
                }

                DivOutput {
                    quotient : Polynomial { coefficients: quotient_coeff },
                    remainder: rem
                }
            }
        }
    }
}

impl Rem for Polynomial {
    type Output = Polynomial;

    fn rem(self, rhs: Polynomial) -> Polynomial {
        let DivOutput { quotient : _, remainder } = self / rhs;

        remainder
    }
}


/// We use the bitwise xor notation (^) to denote exponentiation of the polynomial
impl BitXor<IntPG> for Polynomial {
    type Output = Polynomial;

    fn bitxor(self, exp: IntPG) -> Self::Output {
        if self.is_zero() {
            Polynomial::ZERO
        } else if exp == finite_fields::ZERO {
            Polynomial::ONE()
        } else {
            let mut _base = self.clone();
            let mut _exp = exp;
            let two_ff = finite_fields::constant(I256::from(2));

            let mut res = Polynomial::ONE();
            while _exp > finite_fields::ZERO {
                if _exp % two_ff == finite_fields::ONE {
                    res = res * _base.clone();
                }

                _base = _base.clone() * _base.clone();
                _exp.val >>= 1; // FIXME: investigate why this works, but not %2 on the ff. I suspect it's a problem with the sign of the result!
            }

            res
        }
    }
}

impl Polynomial {
    pub fn new (coefficients : &Vec<IntPG>) -> Polynomial {
        Polynomial { coefficients: coefficients.to_vec() }
    }

    pub const ZERO : Polynomial = Polynomial { coefficients : vec![] };

    #[allow(non_snake_case)]
    pub fn ONE () -> Polynomial {
        Polynomial { coefficients : vec![ finite_fields::ONE ] }
    }

    pub fn degree (&self) -> Degree {
        if self.coefficients.is_empty() {
            Degree::MinusInf
        } else {
            let mut deg = Degree::MinusInf;
            for i in 0..self.coefficients.len() {
                if self.coefficients[i] != finite_fields::ZERO {
                    deg = Degree::Poly(i as u64);
                }
            }

            deg
        }
    }

    pub fn is_zero (&self) -> bool {
        self.degree() == Degree::MinusInf
    }

    pub fn leading_coefficient (&self) -> IntPG {
        match self.degree() {
            Degree::MinusInf => panic! ("Cannot extract the leading coefficient from the ZERO polynomial"),
            Degree::Poly(k) => self.coefficients[k as usize]
        }
    }

    pub fn evaluate (&self, x : &IntPG) -> IntPG {
        let mut xi = finite_fields::ONE;
        let mut value = finite_fields::ZERO;

        for c in &self.coefficients {
            value += (*c) * xi;
            xi *= *x;
        }

        value
    }

    pub fn evaluate_domain (&self, domain : &Vec<IntPG>) -> Vec<IntPG> {
        domain.iter().map(|p| self.evaluate(p)).collect()
    }

    /// Given a non-empty vector of <x, f(x)> pairs computes the polynomial corresponding to the pairs.
    pub fn interpolate (points : &Vec<(IntPG, IntPG)>) -> Self {
        // Panics if no points are given
        assert!(!points.is_empty());

        let (domain, values) : (Vec<IntPG>, Vec<IntPG>) = points.iter().cloned().unzip();
        // We use Langrange interpolation naively
        let x = Polynomial::new(&vec![finite_fields::ZERO, finite_fields::ONE]); // this is x
        let mut res = Polynomial::new(&vec![]); // this is our resulting polynomial, initially empty

        for i in 0..values.len() {
            let mut prod = Polynomial::new(&vec![values[i]]);
            for j in 0..domain.len() {
                if j != i {
                    let xj = Polynomial::new(&vec![domain[j]]);
                    let den = Polynomial::new(&vec![(domain[i] - domain[j]).inverse()]);
                    prod = prod * ((x.clone() - xj) * den);
                }
            }
            res = res + prod;
        }

        res
    }

    /// Returns the (minimal) polynomial vanishing on the given points, i.e.,
    /// Given D = { d1, ..., dn }, the vanishing polynomial (or zerofier) is
    /// (x - d1) ... (x - dn)
    pub fn zerofier (domain : &Vec<IntPG>) -> Polynomial {
        let x = Polynomial::new(&vec![finite_fields::ZERO, finite_fields::ONE]); // this is x
        let mut res = Polynomial::new(&vec![]); // this is our resulting polynomial, initially empty

        for d in domain {
            let di = Polynomial::new(&vec![*d]);
            res = res * (x.clone() - di)
        }

        res
    }

    pub fn scale (self, factor : IntPG) -> Polynomial {
        Polynomial { coefficients : self.coefficients.iter().enumerate().map(|(i, ci)| (
            (factor ^ IntPG::from(i)) * (*ci))
        ).collect() }
    }

    pub fn test_colinearity (points : &Vec<(IntPG, IntPG)>) -> bool {
        let polynomial = Polynomial::interpolate(points);

        polynomial.degree() <= Degree::Poly(1)
    }

}

// A few quick tests
#[cfg(test)]
mod tests {
    use super::*;

    use crypto_bigint::I256;

    #[test]
    fn test_neg () {
        let v = IntPG { val: I256::from(42) };
        assert_eq!(- Polynomial { coefficients: vec![v; 10]}, Polynomial { coefficients: vec![-v; 10]})
    }

    #[test]
    fn test_add () {
        let c1 = IntPG { val : I256::from(42) };
        let c2 = IntPG { val : I256::from(7) };
        let csum1 = IntPG { val : I256::from(49)};
        let csum2 = IntPG { val : I256::from(42)};

        let p1 = Polynomial { coefficients: vec![c1; 10]};
        let p2 = Polynomial { coefficients: vec![c2; 4]};

        let csum_vec = vec![csum1, csum1, csum1, csum1, csum2, csum2, csum2, csum2, csum2, csum2];

        let psum = Polynomial { coefficients: csum_vec};
        assert_eq!(p1 + p2, psum)
    }

    #[test]
    fn test_mul_distr () {
        let a =
            Polynomial {
                coefficients:
                    [0, 5, 5, 2].iter().map(|x| (IntPG { val : I256::from(*x) }) ).collect()
            };
        let b =
            Polynomial {
                coefficients:
                    [2, 2, 1].iter().map(|x| (IntPG { val : I256::from(*x) }) ).collect()
            };

        let c =
            Polynomial {
                coefficients:
                    [0, 5, 2, 5, 5, 1].iter().map(|x| (IntPG { val : I256::from(*x) }) ).collect()
            };

        assert_eq!(a.clone() * (b.clone() + c.clone()), a.clone()*b.clone() + a.clone()*c.clone())
    }
    #[test]
    fn test_mul_comm () {
        let a =
            Polynomial {
                coefficients:
                    [0, 5, 5, 2].iter().map(|x| (IntPG { val : I256::from(*x) }) ).collect()
            };
        let b =
            Polynomial {
                coefficients:
                    [2, 2, 1].iter().map(|x| (IntPG { val : I256::from(*x) }) ).collect()
            };


        assert_eq!(a.clone() * b.clone(), b.clone()*a.clone())
    }

    #[test]
    fn test_div_exact () {
        let a =
            Polynomial {
                coefficients:
                    [1, 0, 5, 2].iter().map(|x| (IntPG { val : I256::from(*x) }) ).collect()
            };
        let b =
            Polynomial {
                coefficients:
                    [2, 2, 1].iter().map(|x| (IntPG { val : I256::from(*x) }) ).collect()
            };

        let DivOutput { quotient, remainder } = (a.clone() * b.clone())/b.clone();
        assert_eq!(quotient, a);
        assert!(remainder.is_zero());
    }

    #[test]
    fn test_div_non_zero_rem () {
        let a =
            Polynomial {
                coefficients:
                    [1, 0, 5, 2].iter().map(|x| (IntPG { val : I256::from(*x) }) ).collect()
            };
        let b =
            Polynomial {
                coefficients:
                    [2, 2, 1].iter().map(|x| (IntPG { val : I256::from(*x) }) ).collect()
            };

        let c =
            Polynomial {
                coefficients:
                    [0, 5, 2, 5, 5, 1].iter().map(|x| (IntPG { val : I256::from(*x) }) ).collect()
            };

        let DivOutput { quotient: _, remainder } = (a.clone() * b.clone())/c.clone();
        assert!(!remainder.is_zero());
    }

    #[test]
    fn test_div_ok () {
        let a =
            Polynomial {
                coefficients:
                    [1, 0, 5, 2].iter().map(|x| (IntPG { val : I256::from(*x) }) ).collect()
            };
        let b =
            Polynomial {
                coefficients:
                    [2, 2, 1].iter().map(|x| (IntPG { val : I256::from(*x) }) ).collect()
            };

        let c =
            Polynomial {
                coefficients:
                    [0, 5, 2, 5, 5, 1].iter().map(|x| (IntPG { val : I256::from(*x) }) ).collect()
            };

        let DivOutput { quotient, remainder } = (a.clone() * b.clone())/c.clone();
        assert_eq!(quotient * c + remainder, a*b);
    }

    #[test]
    fn test_exp () {
        let a =
            Polynomial {
                coefficients:
                    [0, 5, 2, 5, 5, 1].iter().map(|x| (IntPG { val : I256::from(*x) }) ).collect() // x+1
            };

        assert_eq!(a.clone() ^ finite_fields::constant( I256::from(7)), a.clone() * a.clone() * a.clone() * a.clone() * a.clone() * a.clone() * a.clone());
    }

    #[test]
    fn test_interpolate () {
        let pairs: Vec<(IntPG, IntPG)> = [(1, 15), (9, 295), (10, 357)].iter().map(
            |(x, y)|
                (IntPG { val : I256::from(*x) }, IntPG { val : I256::from(*y) })
            ).collect();

        let res = Polynomial::interpolate(&pairs);

        for (x, y) in pairs.clone() {
            assert_eq!(res.evaluate(&x), y);
        }

        assert_eq!(res.degree(), Degree::Poly((pairs.len() - 1) as u64))
    }

    #[test]
    fn test_zerofier () {
        let domain = [0, 5, 2, 5, 5, 1].iter().map(|x| (IntPG { val : I256::from(*x) }) ).collect();

        let res = Polynomial::zerofier(&domain);

        for x in domain {
            assert_eq!(res.evaluate(&x), finite_fields::ZERO);
        }
    }
}
