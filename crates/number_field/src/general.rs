
use nt_polynomial::*;
use nt_traits::*;

/// An element of a general number field
#[derive(Debug, Clone)]
pub struct NFElement<Int: EuclideanDomain + Eq> {
    /// The standard representation of the element (numerator) in terms of a root theta
    pub numer: Polynomial<Int>,
    /// The denominator of the standard representation
    pub d: Int,
    /// T, the underlying polynomial whose root we include
    pub t: Polynomial<Int>,
}

impl<Int: EuclideanDomain + Eq> PartialEq for NFElement<Int> {
    fn eq(&self, other: &Self) -> bool {
        self.numer.mul_constant_ref(other.d) == other.numer.mul_constant_ref(self.d)
    }
}

impl<Int: EuclideanDomain + Eq> NFElement<Int> {
    pub fn inverse(&self) -> Self {
        let (_v, u, gcd) = extended_gcd(self.t.clone(), self.numer.clone());
        assert!(gcd.degree() == 0);

        let tmp1 = NFElement { numer: u.mul_constant_ref(self.d), d: Int::one(), t: self.t.clone() };
        let tmp2 = self.clone() * tmp1.clone();

        NFElement {
            numer: tmp1.numer,
            d: tmp2.numer.leading_coefficient() / tmp2.d,
            t: self.t.clone(),
        }
    }
}
