
use alga::general::*;
use num_traits::PrimInt;

/// A convenience trait to provide a pow() function for alga MultiplicativeMonoids. Automatically implemented for
/// all MultiplicativeMonoids using the Exponentiation by squaring algorithm: https://en.wikipedia.org/wiki/Exponentiation_by_squaring
pub trait Powable {
    fn pow(self, power: u32) -> Self;
}

impl<T: MultiplicativeMonoid> Powable for T {
    fn pow(mut self, mut power: u32) -> Self {
        // https://en.wikipedia.org/wiki/Exponentiation_by_squaring
        if power == 0 {
            return Self::one();
        }
        let mut y = Self::one();
        while power > 1 {
            if power & 1 == 0 {
                self = self.clone() * self.clone();
                power >>= 1;
            } else {
                y = self.clone() * y;
                self = self.clone() * self.clone();
                power = (power - 1) >> 1;
            }
        }
        self * y
    }
}

/// A Euclidean Domain is a ring with some notion of a division algorithm and a GCD function.
/// EuclideanDomain can be trivially implemented for any Field (this implementation is not
/// automatic so as not to collide with the default implementation for PrimInt's) by taking f(x) = 1.
pub trait EuclideanDomain: Ring + ClosedDiv {
    /// Returns the modulus of two elements from the division algorithm
    fn modulus(self, other: Self) -> Self;
    /// The function f as used in https://en.wikipedia.org/wiki/Euclidean_domain.
    fn norm(&self) -> u64;
    /// Take the gcd of two elements. By default uses the Euclidean Algorithm with `norm`.
    fn gcd(mut self, mut b: Self) -> Self {
        if self.norm() < b.norm() {
            std::mem::swap(&mut self, &mut b);
        }
        while !b.is_zero() {
            self = self.modulus(b.clone());
            std::mem::swap(&mut self, &mut b);
        }
        self
    }
}

impl<T: Ring + ClosedDiv + PrimInt> EuclideanDomain for T 
{
    fn modulus(self, other: Self) -> Self {
        self % other
    }

    fn norm(&self) -> u64 {
        self.to_i64().unwrap().abs() as u64
    }
}

/// Computes the GCD of two elements of a EuclideanDomain
pub fn gcd<Int: EuclideanDomain>(a: Int, b: Int) -> Int {
    a.gcd(b)
}

/// Computes the LCM of two elements of a EuclideanDomain
pub fn lcm<Int: EuclideanDomain>(a: Int, b: Int) -> Int {
    // quick optimization
    if a == b {
        a
    } else {
        a.clone() * b.clone() / gcd(a, b)
    }
}
