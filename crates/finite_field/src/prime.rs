use num_traits::*;
use std::ops::{Add, Mul, Div, Neg, Sub, AddAssign, SubAssign, MulAssign, DivAssign};
use alga::general::*;

use nt_traits::{EuclideanDomain, Powable};

fn mod_inverse(num: i64, prime: i64) -> i64 {
        let mut a = prime;
        let mut b = num;
        let mut x = 1;
        let mut y = 0;
        while b != 0 {
                let t = b;
                let q = a / t;
                b = a - q*t;
                a = t;
                let t = x;
                x = y - q*t;
                y = t;
        }
        if y < 0 {
            y + prime
        } else {
            y
        }
}

#[derive(Clone, Copy, Debug, Hash)]
pub struct FPElt {
    pub p: u32,
    pub val: i64,
}

impl FPElt {
    pub fn legendre_symbol(&self) -> i64 {
        self.pow((self.p - 1) / 2).val
    }
    
    // Sourced roughly from https://rosettacode.org/wiki/Tonelli-Shanks_algorithm#Python
    pub fn sqrt(&self) -> Option<FPElt> {
        if self.legendre_symbol() != 1 {
            return None;
        }

        let mut q = self.p - 1;
        let mut s = 0;
        while q % 2 == 0 {
            q /= 2;
            s += 1;
        }
        if s == 1 {
            return Some(self.pow((self.p + 1) / 4));
        }
        let mut z = (self.p as i64) - 1;
        for z_ in 2..self.p {
            if self.p - 1 == (FPElt { val: z_ as i64, p: self.p }).legendre_symbol() as u32 {
                z = z_ as i64;
                break;
            }
        }

        let mut c = FPElt { val: z, p: self.p }.pow(q);
        let mut r = self.pow((q + 1) / 2);
        let mut t = self.pow(q);
        let mut m = s;
        let mut t2;

        while (t - One::one()) != Zero::zero() {
            t2 = t * t;
            let mut i = m - 1;
            for i_ in 1..m {
                if t2 - One::one() == Zero::zero() {
                    i = i_;
                    break;
                }
                t2 = t2 * t2;
            }
            let b = c.pow(1 << (m - i - 1));
            r = r * b;
            c = b * b;
            t = t * c;
            m = i;
        }
        Some(r)
    }
}

impl std::fmt::Display for FPElt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val)
    }
}

impl std::cmp::PartialEq for FPElt {
    fn eq(&self, other: &Self) -> bool {
        self.val == other.val
    }
}

impl Eq for FPElt {}

impl Add for FPElt {
    type Output = FPElt;

    fn add(self, other: FPElt) -> FPElt {
        if self.p == 0 && other.p == 0 { 
            return FPElt {
                p: 0,
                val: self.val + other.val,
            };
        }
        let p = if self.p == 0 { other.p } else { self.p };
        // TODO: Maybe this should use checked_add
        FPElt {
            p,
            val: (self.val + other.val).rem_euclid(p as i64)
        }
    }
}

impl AddAssign for FPElt {
    fn add_assign(&mut self, other: FPElt) {
        *self = *self + other;
    }
}

impl Sub for FPElt {
    type Output = FPElt;

    fn sub(self, other: FPElt) -> FPElt {
        if self.p == 0 && other.p == 0 { 
            return FPElt {
                p: 0,
                val: self.val - other.val,
            };
        }
        let p = if self.p == 0 { other.p } else { self.p };
        FPElt {
            p,
            val: (self.val - other.val).rem_euclid(p as i64)
        }
    }
}

impl SubAssign for FPElt {
    fn sub_assign(&mut self, other: FPElt) {
        *self = *self - other;
    }
}

impl Mul for FPElt {
    type Output = FPElt;

    fn mul(self, other: FPElt) -> FPElt {
        if self.p == 0 && other.p == 0 { 
            return FPElt {
                p: 0,
                val: self.val * other.val,
            };
        }
        let p = if self.p == 0 { other.p } else { self.p };
        FPElt {
            p,
            val: (self.val * other.val).rem_euclid(p as i64)
        }
    }
}

impl MulAssign for FPElt {
    fn mul_assign(&mut self, other: FPElt) {
        *self = *self * other;
    }
}

impl Div for FPElt {
    type Output = FPElt;

    fn div(self, other: FPElt) -> FPElt {
        self * (<Self as TwoSidedInverse<Multiplicative>>::two_sided_inverse(&other))
    }
}

impl DivAssign for FPElt {
    fn div_assign(&mut self, other: FPElt) {
        *self = *self / other;
    }
}

impl Neg for FPElt {
    type Output = FPElt;

    fn neg(self) -> FPElt {
        if self.p == 0 {
            return FPElt {
                p: self.p,
                val: -self.val,
            };
        }
        FPElt {
            p: self.p,
            val: (-self.val).rem_euclid(self.p as i64)
        }
    }
}

impl One for FPElt {
    fn one() -> Self {
        FPElt {
            p: 0,
            val: 1
        }
    }
}

impl Zero for FPElt {
    fn is_zero(&self) -> bool {
        self.val == 0
    }

    fn zero() -> Self {
        FPElt {
            p: 0,
            val: 0,
        }
    }
}

impl AbstractMagma<Additive> for FPElt {
    fn operate(&self, right: &Self) -> Self {
        *self + *right
    }
}

impl Identity<Additive> for FPElt {
    fn identity() -> Self {
        FPElt {
            p: 0,
            val: 0,
        }
    }
}

impl TwoSidedInverse<Additive> for FPElt {
    fn two_sided_inverse(&self) -> Self {
        -*self
    }
}

impl AbstractQuasigroup<Additive> for FPElt {}
impl AbstractLoop<Additive> for FPElt {}
impl AbstractSemigroup<Additive> for FPElt {}
impl AbstractMonoid<Additive> for FPElt {}
impl AbstractGroup<Additive> for FPElt {}
impl AbstractGroupAbelian<Additive> for FPElt {}

impl AbstractMagma<Multiplicative> for FPElt {
    fn operate(&self, right: &Self) -> Self {
        *self * *right
    }
}

impl Identity<Multiplicative> for FPElt {
    fn identity() -> Self {
        FPElt {
            p: 0,
            val: 1,
        }
    }
}

impl TwoSidedInverse<Multiplicative> for FPElt {
    fn two_sided_inverse(&self) -> Self {
        FPElt {
            p: self.p,
            val: mod_inverse(self.val, self.p as i64),
        }
    }
}

impl AbstractQuasigroup<Multiplicative> for FPElt {}
impl AbstractLoop<Multiplicative> for FPElt {}
impl AbstractSemigroup<Multiplicative> for FPElt {}
impl AbstractMonoid<Multiplicative> for FPElt {}
impl AbstractGroup<Multiplicative> for FPElt {}
impl AbstractGroupAbelian<Multiplicative> for FPElt {}

impl AbstractRing<Additive, Multiplicative> for FPElt {}
impl AbstractRingCommutative<Additive, Multiplicative> for FPElt {}
impl AbstractField<Additive, Multiplicative> for FPElt {}


// Trivial implementation for a field
impl EuclideanDomain for FPElt {
    fn modulus(self, other: Self) -> Self {
        let p = if self.p == 0 { other.p } else { self.p };
        FPElt {
            val: 0,
            p
        }
    }

    fn norm(&self) -> u64 {
        0
    }

    fn gcd(self, other: Self) -> Self {
        let p = if self.p == 0 { other.p } else { self.p };
        FPElt {
            val: 1,
            p
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_misc_pow() {
        let val = FPElt { val: 2, p: 1000000 };
        assert!(val.pow(4).val == 16);
    }

    #[test]
    fn test_fp_sqrt() {
        let mut ct = 0;
        for x in [1023, 32, 1003, 329, 643, 1, 2, 0].iter() {
            for p in [1591, 1513, 2345, 53252, 99199].iter() {
                let val = FPElt { val: *x, p: *p };
                match val.sqrt() {
                    Some(val2) => {ct += 1; assert_eq!(val2 * val2, val)},
                    _ => {}
                }
            }
        }
        dbg!(ct);
    }
}

