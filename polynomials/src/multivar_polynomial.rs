use std::collections::HashMap;
use std::ops::{Add, BitXor, Mul, Neg, Sub};

use finite_fields::IntPG;
use crate::polynomial::Polynomial;


/// We use the same representation as STARK's anatomy tutorial, which is called a monomial map
/// An MPolynomial represents multivariable polynomials as dictionaries mapping
/// vectors of exponents (monomials) to their coefficients, i.e.,
///     17 + 2xy + 42z - 19x^6*y^3*z^12
/// is denoted as
///
/// [0, 0, 0] -> 17
/// [1, 1, 0] -> 2
/// [0, 0, 1] -> 42
/// [6, 3, 12] -> -19
///
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MPolynomial {
    monomial_map : HashMap<Vec<IntPG>, IntPG>
}

impl Neg for MPolynomial {
    type Output = Self;

    fn neg (self) -> MPolynomial {

        let coeff_map_neg = self.monomial_map.iter().map(|(k, v)| (k.clone(), -(*v))).collect();

        MPolynomial { monomial_map: coeff_map_neg }
    }
}

impl Add for MPolynomial {
    type Output = Self;
    fn add (self, rhs : MPolynomial) -> MPolynomial {
        if self.monomial_map.is_empty() {
            rhs
        } else if rhs.monomial_map.is_empty() {
            self
        } else {
            let mut res_map = HashMap::<Vec<IntPG>, IntPG>::new();

            // Compute the number of variables in the resulting polynomial
            let num_variables = usize::max(self.monomial_map.keys().map(|k| k.len()).max().unwrap(), rhs.monomial_map.keys().map(|k| k.len()).max().unwrap());

            // Now, go over each pair in the monomial_map of self, modify the key with proper padding according to num_variables and insert the new association in res_map
            for (k, v) in self.monomial_map {
                let mut padded_key = k.clone();
                padded_key.append(&mut vec![IntPG::ZERO; num_variables - k.len()]);

                assert_eq!(res_map.insert(padded_key, v), None);
            }

            // This is similar to the above, except that if the mapping already exists we need to updated said mapping with the appropriate sum of coefficients
            for (k, v) in rhs.monomial_map {
                let mut padded_key = k.clone();
                padded_key.append(&mut vec![IntPG::ZERO; num_variables - k.len()]);

                match res_map.get(&k) {
                    None => res_map.insert(padded_key, v),
                    Some(old_v) => res_map.insert(padded_key, *old_v + v)
                };
            }

            MPolynomial::new(res_map)
        }
    }
}


impl Sub for MPolynomial {
    type Output = Self;

    fn sub (self, rhs : MPolynomial) -> MPolynomial {
        self.add (-rhs)
    }
}

impl Mul for MPolynomial {
    type Output = Self;

    fn mul(self, rhs: MPolynomial) -> MPolynomial {
        let mut res_map = HashMap::<Vec<IntPG>, IntPG>::new();
        // Compute the number of variables in the resulting polynomial
        let num_variables = usize::max(self.monomial_map.keys().map(|k| k.len()).max().unwrap(), rhs.monomial_map.keys().map(|k| k.len()).max().unwrap());

        for (k0, v0) in &self.monomial_map {
            for (k1, v1) in &rhs.monomial_map {
                let mut monomial = vec![IntPG::ZERO; num_variables];

                for i in 0..k0.len() {
                    monomial[i] += k0[i];
                }

                for i in 0..k1.len() {
                    monomial[i] += k1[i];
                }

                match res_map.get(&monomial) {
                    None => res_map.insert(monomial, (*v0)*(*v1)),
                    Some(old_v) => res_map.insert(monomial, *old_v + (*v0)*(*v1))
                };
            }
        }

        MPolynomial::new(res_map)
    }
}

/// We use the bitwise xor notation (^) to denote exponentiation of the multivariate polynomial
impl BitXor<IntPG> for MPolynomial {
    type Output = MPolynomial;

    fn bitxor(self, exp: IntPG) -> MPolynomial {
        if self.is_zero() {
            MPolynomial::ZERO()
        } else if exp == IntPG::ZERO {
            MPolynomial::ONE()
        } else {
            let mut _base = self.clone();
            let mut _exp = exp;
            let two_ff = IntPG::from(2);

            let mut res = MPolynomial::ONE();
            while _exp > IntPG::ZERO {
                if _exp % two_ff == IntPG::ONE {
                    res = res * _base.clone();
                }

                _base = _base.clone() * _base.clone();
                _exp >>= 1; // FIXME: investigate if this works
            }

            res
        }
    }
}

/// We use the bitwise xor notation (^) to denote exponentiation of the multivariate polynomial (also on native type usize)
impl BitXor<usize> for MPolynomial {
    type Output = MPolynomial;

    fn bitxor(self, exp: usize) -> MPolynomial {
        if self.is_zero() {
            MPolynomial::ZERO()
        } else if exp == 0 {
            MPolynomial::ONE()
        } else {
            let mut _base = self.clone();
            let mut _exp = exp;

            let mut res = MPolynomial::ONE();
            while _exp > 0 {
                if _exp % 2 == 1 {
                    res = res * _base.clone();
                }

                _base = _base.clone() * _base.clone();
                _exp >>= 1;
            }

            res
        }
    }
}

impl MPolynomial {
    pub fn new (monomial_map: HashMap<Vec<IntPG>, IntPG>) -> MPolynomial {
        MPolynomial { monomial_map }
    }

    #[allow(non_snake_case)]
    pub fn ZERO () -> MPolynomial {
        MPolynomial { monomial_map : HashMap::new() }
    }

    pub fn constant (c : IntPG) -> MPolynomial {
        let mut monomial_map = HashMap::new();
        monomial_map.insert(vec![IntPG::ZERO], c);

        MPolynomial { monomial_map }
    }

    #[allow(non_snake_case)]
    pub fn ONE () -> MPolynomial {
        MPolynomial::constant(IntPG::ONE)
    }

    pub fn is_zero (&self) -> bool {
        self.monomial_map.is_empty() || self.monomial_map.values().all(|v| *v == IntPG::ZERO)
    }

    pub fn variables (num_variables : usize) -> Vec<MPolynomial> {
        let mut variables = Vec::new();

        for i in 0..num_variables {
            let mut monomial_map_key = vec![IntPG::ZERO; i];
            monomial_map_key.extend(vec![IntPG::ONE; 1]);
            monomial_map_key.extend(vec![IntPG::ZERO; num_variables - i - 1]);

            let mut monomial_map = HashMap::new();
            monomial_map.insert(monomial_map_key, IntPG::ONE);

            let variable = MPolynomial::new(monomial_map);
            variables.push(variable);
        }

        variables
    }

    pub fn lift (polynomial : Polynomial, variable_index : usize) -> MPolynomial {
        if polynomial.is_zero() {
            MPolynomial::ZERO()
        } else {
            let variables = MPolynomial::variables(variable_index+1);
            let x = &variables[variable_index];

            polynomial.coefficients.iter().enumerate().fold(MPolynomial::ZERO(), |acc, (i, c)| acc + MPolynomial::constant(*c) * (x.clone() ^ i))
        }
    }

    pub fn evaluate (&self, point : Vec<IntPG>) -> IntPG {
        let mut value = IntPG::ZERO;

        for (k, v) in &self.monomial_map {
            let mut monomial_value = *v;
            for i in 0..k.len() {
                monomial_value *= point[i] ^ k[i];
            }

            value += monomial_value;
        }

        value
    }

    pub fn evaluate_symbolic (&self, point : Vec<Polynomial>) -> Polynomial {
        let mut value = Polynomial::ZERO;

        for (k, v) in &self.monomial_map {
            let mut prod = Polynomial::new(&[*v; 1]);
            for i in 0..k.len() {
                prod = prod * (point[i].clone() ^ k[i]);
            }

            value = value + prod;
        }

        value
    }
}

// A few quick tests
#[cfg(test)]
mod tests {
    // use super::*;

    // use crypto_bigint::I512;

    // #[test]
    // fn test_neg () {
    //     let v = MPolynomial::constant(IntPG { val: I512::from(42) });
    //     let mv = MPolynomial::constant(IntPG { val: I512::from(-42) });
    //     assert_eq!(-v, mv)
    // }

    // #[test]
    // fn test_add () {
    //     let c1 = IntPG { val : I512::from(42) };
    //     let c2 = IntPG { val : I512::from(7) };
    //     let csum1 = IntPG { val : I512::from(49)};
    //     let csum2 = IntPG { val : I512::from(42)};

    //     let p1 = Polynomial { coefficients: vec![c1; 10]};
    //     let p2 = Polynomial { coefficients: vec![c2; 4]};

    //     let csum_vec = vec![csum1, csum1, csum1, csum1, csum2, csum2, csum2, csum2, csum2, csum2];

    //     let psum = Polynomial { coefficients: csum_vec};
    //     assert_eq!(p1 + p2, psum)
    // }

    // #[test]
    // fn test_mul_distr () {
    //     let a =
    //         Polynomial {
    //             coefficients:
    //                 [0, 5, 5, 2].iter().map(|x| (IntPG { val : I512::from(*x) }) ).collect()
    //         };
    //     let b =
    //         Polynomial {
    //             coefficients:
    //                 [2, 2, 1].iter().map(|x| (IntPG { val : I512::from(*x) }) ).collect()
    //         };

    //     let c =
    //         Polynomial {
    //             coefficients:
    //                 [0, 5, 2, 5, 5, 1].iter().map(|x| (IntPG { val : I512::from(*x) }) ).collect()
    //         };

    //     assert_eq!(a.clone() * (b.clone() + c.clone()), a.clone()*b.clone() + a.clone()*c.clone())
    // }
    // #[test]
    // fn test_mul_comm () {
    //     let a =
    //         Polynomial {
    //             coefficients:
    //                 [0, 5, 5, 2].iter().map(|x| (IntPG { val : I512::from(*x) }) ).collect()
    //         };
    //     let b =
    //         Polynomial {
    //             coefficients:
    //                 [2, 2, 1].iter().map(|x| (IntPG { val : I512::from(*x) }) ).collect()
    //         };


    //     assert_eq!(a.clone() * b.clone(), b.clone()*a.clone())
    // }

    // #[test]
    // fn test_div_exact () {
    //     let a =
    //         Polynomial {
    //             coefficients:
    //                 [1, 0, 5, 2].iter().map(|x| (IntPG { val : I512::from(*x) }) ).collect()
    //         };
    //     let b =
    //         Polynomial {
    //             coefficients:
    //                 [2, 2, 1].iter().map(|x| (IntPG { val : I512::from(*x) }) ).collect()
    //         };

    //     let DivOutput { quotient, remainder } = (a.clone() * b.clone())/b.clone();
    //     assert_eq!(quotient, a);
    //     assert!(remainder.is_zero());
    // }

    // #[test]
    // fn test_div_non_zero_rem () {
    //     let a =
    //         Polynomial {
    //             coefficients:
    //                 [1, 0, 5, 2].iter().map(|x| (IntPG { val : I512::from(*x) }) ).collect()
    //         };
    //     let b =
    //         Polynomial {
    //             coefficients:
    //                 [2, 2, 1].iter().map(|x| (IntPG { val : I512::from(*x) }) ).collect()
    //         };

    //     let c =
    //         Polynomial {
    //             coefficients:
    //                 [0, 5, 2, 5, 5, 1].iter().map(|x| (IntPG { val : I512::from(*x) }) ).collect()
    //         };

    //     let DivOutput { quotient: _, remainder } = (a.clone() * b.clone())/c.clone();
    //     assert!(!remainder.is_zero());
    // }

    // #[test]
    // fn test_div_ok () {
    //     let a =
    //         Polynomial {
    //             coefficients:
    //                 [1, 0, 5, 2].iter().map(|x| (IntPG { val : I512::from(*x) }) ).collect()
    //         };
    //     let b =
    //         Polynomial {
    //             coefficients:
    //                 [2, 2, 1].iter().map(|x| (IntPG { val : I512::from(*x) }) ).collect()
    //         };

    //     let c =
    //         Polynomial {
    //             coefficients:
    //                 [0, 5, 2, 5, 5, 1].iter().map(|x| (IntPG { val : I512::from(*x) }) ).collect()
    //         };

    //     let DivOutput { quotient, remainder } = (a.clone() * b.clone())/c.clone();
    //     assert_eq!(quotient * c + remainder, a*b);
    // }

    // #[test]
    // fn test_exp () {
    //     let a =
    //         Polynomial {
    //             coefficients:
    //                 [0, 5, 2, 5, 5, 1].iter().map(|x| (IntPG { val : I512::from(*x) }) ).collect() // x+1
    //         };

    //     assert_eq!(a.clone() ^ 7, a.clone() * a.clone() * a.clone() * a.clone() * a.clone() * a.clone() * a.clone());
    // }

    // #[test]
    // fn test_interpolate () {
    //     let pairs: Vec<(IntPG, IntPG)> = [(1, 15), (9, 295), (10, 357)].iter().map(
    //         |(x, y)|
    //             (IntPG { val : I512::from(*x) }, IntPG { val : I512::from(*y) })
    //         ).collect();

    //     let res = Polynomial::interpolate(&pairs);

    //     for (x, y) in pairs.clone() {
    //         assert_eq!(res.evaluate(&x), y);
    //     }

    //     assert_eq!(res.degree(), Degree::Poly((pairs.len() - 1) as u64))
    // }

    // #[test]
    // fn test_zerofier () {
    //     let domain = [0, 5, 2, 5, 5, 1].iter().map(|x| (IntPG { val : I512::from(*x) }) ).collect();

    //     let res = Polynomial::zerofier(&domain);

    //     for x in domain {
    //         assert_eq!(res.evaluate(&x), IntPG::ZERO);
    //     }
    // }
}

