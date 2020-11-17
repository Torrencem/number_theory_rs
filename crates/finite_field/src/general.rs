
use crate::prime::FPElt;
use nt_polynomial::*;
use nt_traits::*;
use num_traits::{Zero, One};

use std::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign, Div, DivAssign, Neg};

use alga::general::*;

#[derive(Clone, Debug)]
/// An element of the finite field F_{p^n}, for prime p and natural number n
pub struct FPnElt {
    /// A representative of the equivalence class of F_p[x] / <r(x)>
    val: Polynomial<FPElt>,
    /// A polynomial r(x) whose ideal is irreducible over F_p[x]
    r: Polynomial<FPElt>,
}

impl std::cmp::PartialEq for FPnElt {
    fn eq(&self, other: &FPnElt) -> bool {
        self.val == other.val
    }
}

impl std::cmp::Eq for FPnElt { }

impl FPnElt {
    // pub fn p(&self) -> u32 {
    //     self.r.data()[0].p
    // }
    //
    // pub fn n(&self) -> usize {
    //     self.r.degree()
    // }

    pub fn new(val: Polynomial<FPElt>, p: u32, n: usize) -> Self {
        FPnElt {
            val,
            r: find_irreducible(p, n),
        }
    }
}

/// Find an irreducible element of F_p[x] by brute force search
fn find_irreducible(p: u32, n: usize) -> Polynomial<FPElt> {
    let mut contents: Vec<FPElt> = vec![FPElt { val: 0, p }; n];
    // Start search at x^n + 1
    contents.push(FPElt { val: 1, p });
    // Search through all polynomials
    let mut poly_val = 1;
    loop {
        // Turn poly_val into a polynomial based on its digits in base p
        for i in 0..n - 1 {
            contents[i] = FPElt { val: ((poly_val % p.pow((i + 1) as u32)) / p.pow(i as u32)) as i64, p };
        }
        let poly = Polynomial::new(contents.clone());
        if is_irreducible(&poly) {
            return poly;
        }
        poly_val += 1;
    }
}

/// Check if a polynomial in F_p[x] is irreducible (more precisely, if its ideal is irreducible)
pub fn is_irreducible(r: &Polynomial<FPElt>) -> bool {
    // Based on Chapter 10 from johnkerl:
    // https://johnkerl.org/doc/ffcomp.pdf#page=43
    let p = r.data()[0].p;
    let m = r.degree();
    let x = Polynomial::new(vec![FPElt { val: 0, p }, FPElt { val: 1, p }]);
    let mut u = x.clone();
    for _ in 1..m {
        u = u.pow(p);
        u = u.modulus(r.clone());
        let g = gcd(r.clone(), u.clone() - x.clone());
        if g.degree() != 0 || g.is_zero() {
            return false;
        }
    }
    true
}

// These impls are analogous to prime.rs

impl Add for FPnElt {
    type Output = FPnElt;

    fn add(self, other: FPnElt) -> FPnElt {
        if self.r.is_zero() && other.r.is_zero() {
            return FPnElt {
                r: Zero::zero(),
                val: self.val + other.val,
            }
        }
        let r = if self.r.is_zero() { other.r.clone() } else { self.r.clone() };
        FPnElt {
            val: (self.val + other.val).modulus(r.clone()),
            r,
        }
    }
}

impl AddAssign for FPnElt {
    fn add_assign(&mut self, rhs: FPnElt) {
        *self = self.clone() + rhs;
    }
}

impl Sub for FPnElt {
    type Output = FPnElt;

    fn sub(self, other: FPnElt) -> FPnElt {
        if self.r.is_zero() && other.r.is_zero() {
            return FPnElt {
                r: Zero::zero(),
                val: self.val - other.val,
            }
        }
        let r = if self.r.is_zero() { other.r.clone() } else { self.r.clone() };
        FPnElt {
            val: (self.val - other.val).modulus(r.clone()),
            r,
        }
    }
}

impl SubAssign for FPnElt {
    fn sub_assign(&mut self, rhs: FPnElt) {
        *self = self.clone() - rhs;
    }
}

impl Mul for FPnElt {
    type Output = FPnElt;

    fn mul(self, other: FPnElt) -> FPnElt {
        if self.r.is_zero() && other.r.is_zero() {
            return FPnElt {
                r: Zero::zero(),
                val: self.val * other.val,
            }
        }
        let r = if self.r.is_zero() { other.r.clone() } else { self.r.clone() };
        FPnElt {
            val: (self.val * other.val).modulus(r.clone()),
            r,
        }
    }
}

impl MulAssign for FPnElt {
    fn mul_assign(&mut self, rhs: FPnElt) {
        *self = self.clone() * rhs;
    }
}

impl Div for FPnElt {
    type Output = FPnElt;

    fn div(self, other: FPnElt) -> FPnElt {
        self * (<Self as TwoSidedInverse<Multiplicative>>::two_sided_inverse(&other))
    }
}

impl DivAssign for FPnElt {
    fn div_assign(&mut self, rhs: FPnElt) {
        *self = self.clone() / rhs
    }
}

impl Neg for FPnElt {
    type Output = FPnElt;

    fn neg(self) -> FPnElt {
        if self.r.is_zero() {
            return FPnElt {
                r: Zero::zero(),
                val: -self.val,
            }
        }
        FPnElt {
            r: self.r.clone(),
            val: (-self.val).modulus(self.r),
        }
    }
}

impl One for FPnElt {
    fn one() -> Self {
        FPnElt {
            r: Zero::zero(),
            val: One::one(),
        }
    }
}

impl Zero for FPnElt {
    fn is_zero(&self) -> bool {
        self.val.is_zero()
    }

    fn zero() -> Self {
        FPnElt {
            r: Zero::zero(),
            val: Zero::zero(),
        }
    }
}

impl AbstractMagma<Additive> for FPnElt {
    fn operate(&self, right: &Self) -> Self {
        self.clone() + right.clone()
    }
}

impl Identity<Additive> for FPnElt {
    fn identity() -> Self {
        Zero::zero()
    }
}

impl TwoSidedInverse<Additive> for FPnElt {
    fn two_sided_inverse(&self) -> Self {
        -self.clone()
    }
}

impl AbstractQuasigroup<Additive> for FPnElt {}
impl AbstractLoop<Additive> for FPnElt {}
impl AbstractSemigroup<Additive> for FPnElt {}
impl AbstractMonoid<Additive> for FPnElt {}
impl AbstractGroup<Additive> for FPnElt {}
impl AbstractGroupAbelian<Additive> for FPnElt {}

impl AbstractMagma<Multiplicative> for FPnElt {
    fn operate(&self, right: &Self) -> Self {
        self.clone() * right.clone()
    }
}

impl Identity<Multiplicative> for FPnElt {
    fn identity() -> Self {
        One::one()
    }
}

impl TwoSidedInverse<Multiplicative> for FPnElt {
    fn two_sided_inverse(&self) -> Self {
        // As described in https://johnkerl.org/doc/ffcomp.pdf
        todo!("Multiplicative inverse using Bezout coefficients and extended_gcd")
    }
}

impl AbstractQuasigroup<Multiplicative> for FPnElt {}
impl AbstractLoop<Multiplicative> for FPnElt {}
impl AbstractSemigroup<Multiplicative> for FPnElt {}
impl AbstractMonoid<Multiplicative> for FPnElt {}
impl AbstractGroup<Multiplicative> for FPnElt {}
impl AbstractGroupAbelian<Multiplicative> for FPnElt {}

impl AbstractRing<Additive, Multiplicative> for FPnElt {}
impl AbstractRingCommutative<Additive, Multiplicative> for FPnElt {}
impl AbstractField<Additive, Multiplicative> for FPnElt {}

// Trivial implementation for a field
impl EuclideanDomain for FPnElt {
    fn modulus(self, other: Self) -> Self {
        let r = if self.r.is_zero() { other.r.clone() } else { self.r.clone() };
        FPnElt {
            val: Zero::zero(),
            r
        }
    }

    fn norm(&self) -> u64 {
        0
    }

    fn gcd(self, other: Self) -> Self {
        let r = if self.r.is_zero() { other.r } else { self.r };
        FPnElt {
            val: One::one(),
            r
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_irr() {
        let p = Polynomial::new(vec![FPElt { val: 1, p: 541 }, FPElt { val: 1, p: 541 }, FPElt { val: 1, p: 541 }]);
        let p_prime = FPnElt::new(p, 541, 3);
        // x^3 + 2 is irreducible, and is the first irreducible one in order.
        assert_eq!(p_prime.r.data(), &[FPElt { val: 2, p: 541 }, FPElt { val: 0, p: 541 }, FPElt { val: 0, p: 541 }, FPElt { val: 1, p: 541 }]);
    }

    #[test]
    fn poly_test() {
        // TODO: Ask conceicao about this
        let p = Polynomial::new(vec![
        FPElt {
                p: 13,
                val: 4,
        },
        FPElt {
            p: 13,
            val: 1,
        },
        FPElt {
            p: 13,
            val: 0,
        },
        FPElt {
            p: 13,
            val: 0,
        },
        FPElt {
            p: 13,
            val: 0,
        },
        FPElt {
            p: 13,
            val: 1,
        },
        ]);
        let q = Polynomial::new(vec![
        FPElt {
            p: 13,
            val: 6,
        },
        FPElt {
            p: 13,
            val: 7,
        },
        FPElt {
            p: 13,
            val: 5,
        },
        FPElt {
            p: 13,
            val: 7,
        },
        FPElt {
            p: 13,
            val: 1,
        },
        ]);
        let (u, v, g) = extended_gcd(p.clone(), q.clone());
        dbg!(p.clone() * u.clone() + q.clone() * v.clone());
        dbg!(u.degree());
        dbg!(q.degree() - g.degree());
        dbg!(v.degree());
        dbg!(p.degree() - g.degree());
    }
}
