
use std::ops::{Add, Div, Mul, Sub};

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Copy, Clone)]
pub enum Degree {
    MinusInf,
    Poly (u64)
}

impl Degree {
    pub fn unwrap (self) -> u64 {
        match self {
            Degree::MinusInf => panic!("Cannot unwrap a -inf degree"),
            Degree::Poly(n) => n
        }
    }
}

impl Add for Degree {
    type Output = Self;

    fn add (self, rhs : Degree) -> Degree {
        match (self, rhs) {
            (Degree::MinusInf, _) | (_, Degree::MinusInf) => Degree::MinusInf,
            (Degree::Poly(n), Degree::Poly(m)) => Degree::Poly(m+n)
        }
    }
}

impl Sub for Degree {
    type Output = Self;

    fn sub (self, rhs : Degree) -> Degree {
        match (self, rhs) {
            (Degree::MinusInf, _) | (_, Degree::MinusInf) => Degree::MinusInf,
            (Degree::Poly(n), Degree::Poly(m)) => Degree::Poly(n-m)
        }
    }
}

impl Mul for Degree {
    type Output = Self;

    fn mul (self, rhs : Degree) -> Degree {
        match (self, rhs) {
            (Degree::MinusInf, _) | (_, Degree::MinusInf) => Degree::MinusInf,
            (Degree::Poly(n), Degree::Poly(m)) => Degree::Poly(m*n)
        }
    }
}

impl Div for Degree {
    type Output = Self;

    fn div (self, rhs : Degree) -> Degree {
        match (self, rhs) {
            (Degree::MinusInf, _) | (_, Degree::MinusInf) => Degree::MinusInf,
            (Degree::Poly(n), Degree::Poly(m)) => Degree::Poly(m/n)
        }
    }
}
