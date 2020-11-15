//! Polynomial data type. The core type is a fork of the ``polynomial`` crate. This crate contains
//! extra implementations of ``alga`` traits, as well as gcd and resultant algorithms.

extern crate num_traits;
extern crate nt_traits;
extern crate alga;

use num_traits::{One, Zero, PrimInt};
use std::ops::{Add, Mul, Div, Neg, Sub, AddAssign, SubAssign, MulAssign, DivAssign};
use std::{cmp, fmt};
use alga::general::*;
use nt_traits::{EuclideanDomain, gcd};

/// A polynomial expression with coefficients in ``T``
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Polynomial<T> {
    data: Vec<T>,
}

// Implementations of alga traits for Polynomial<T>

impl<T: Ring> Identity<Additive> for Polynomial<T> {
    fn identity() -> Self {
        <Self as One>::one()
    }
}
impl<T: Ring> AbstractMagma<Additive> for Polynomial<T> {
    fn operate(&self, right: &Self) -> Self {
        self + right
    }
}
impl<T: Ring> AbstractSemigroup<Additive> for Polynomial<T> {}
impl<T: Ring> AbstractMonoid<Additive> for Polynomial<T> {}
impl<T: Ring> TwoSidedInverse<Additive> for Polynomial<T> {
    fn two_sided_inverse(&self) -> Self {
        -self
    }
}
impl<T: Ring> AbstractQuasigroup<Additive> for Polynomial<T> {}
impl<T: Ring> AbstractLoop<Additive> for Polynomial<T> {}
impl<T: Ring> AbstractGroup<Additive> for Polynomial<T> {}
impl<T: Ring> AbstractGroupAbelian<Additive> for Polynomial<T> {}
impl<T: Ring> Identity<Multiplicative> for Polynomial<T> {
    fn identity() -> Self {
        <Self as Zero>::zero()
    }
}
impl<T: Ring> AbstractMagma<Multiplicative> for Polynomial<T> {
    fn operate(&self, right: &Self) -> Self {
        self * right
    }
}
impl<T: Ring> AbstractSemigroup<Multiplicative> for Polynomial<T> {}
impl<T: Ring> AbstractMonoid<Multiplicative> for Polynomial<T> {}
impl<T: Ring> AbstractRing<Additive, Multiplicative> for Polynomial<T> {}
// impl<T: Ring> Ring for Polynomial<T> {} // (implicit)

impl<T: Zero> Polynomial<T> {
    /// Creates new `Polynomial`.
    ///
    /// ```rust
    /// use polynomial::Polynomial;
    /// let poly = Polynomial::new(vec![1, 2, 3]);
    /// assert_eq!("1+2*x+3*x^2", poly.pretty("x"));
    /// ```
    #[inline]
    pub fn new(mut data: Vec<T>) -> Polynomial<T> {
        while let Some(true) = data.last().map(|x| x.is_zero()) {
            let _ = data.pop();
        }
        Polynomial { data }
    }

    /// Gets the degree of the polynomial
    pub fn degree(&self) -> usize {
        self.data.len().saturating_sub(1)
    }
}

impl<T: Zero + One + Clone> Polynomial<T> {
    /// Evaluates the polynomial value.
    ///
    /// ```rust
    /// use polynomial::Polynomial;
    /// let poly = Polynomial::new(vec![1, 2, 3]);
    /// assert_eq!(1, poly.eval(0));
    /// assert_eq!(6, poly.eval(1));
    /// assert_eq!(17, poly.eval(2));
    /// ```
    #[inline]
    pub fn eval(&self, x: T) -> T {
        let mut sum: T = Zero::zero();
        let mut x_n: T = One::one();
        for n in self.data.iter() {
            sum = sum + n.clone() * x_n.clone();
            x_n = x_n * x.clone();
        }
        sum
    }
}

impl<T> Polynomial<T> {
    /// Gets the slice of internal data.
    #[inline]
    pub fn data(&self) -> &[T] {
        &self.data
    }

    /// Gets the leading coefficient of the polynomial
    #[inline]
    pub fn leading_coefficient(&self) -> &T {
        &self.data[0]
    }
    
    /// Multiply the polynomial by a constant
    pub fn mul_constant<V: Mul<T> + Clone>(self, constant: V) -> Polynomial<<V as Mul<T>>::Output> {
        Polynomial {
            data: self.data.into_iter()
                .map(|val| constant.clone() * val)
                .collect()
        }
    }

    /// Divide the polynomial by a constant
    pub fn div_constant<V: Clone>(self, constant: V) -> Polynomial<<T as Div<V>>::Output> 
    where T: Div<V> {
        Polynomial {
            data: self.data.into_iter()
                .map(|val| val / constant.clone())
                .collect()
        }
    }

    /// Add a constant to the polynomial
    pub fn add_constant<V>(mut self, constant: V) -> Polynomial<T>
    where T: AddAssign<V> {
        self.data[0] += constant;
        self
    }
}

impl<T: Clone> Polynomial<T> {
    /// Add a constant to a reference to the polynomial
    pub fn add_constant_ref<V>(&self, constant: V) -> Polynomial<T> 
    where T: AddAssign<V> {
        let mut data = self.data.clone();
        data[0] += constant;
        Polynomial { data }
    }
    
    /// Multiply a reference to the polynomial by a constant
    pub fn mul_constant_ref<V: Mul<T> + Clone>(&self, constant: V) -> Polynomial<<V as Mul<T>>::Output> {
        Polynomial {
            data: self.data.iter()
                .cloned()
                .map(|val| constant.clone() * val)
                .collect()
        }
    }

    /// Divide a reference to the polynomial by a constant
    pub fn div_constant_ref<V: Clone>(&self, constant: V) -> Polynomial<<T as Div<V>>::Output>
    where T: Div<V>
    {
        Polynomial {
            data: self.data.iter()
                .cloned()
                .map(|val| val / constant.clone())
                .collect()
        }
    }
}

impl<T: Ring + Clone> Polynomial<T> {
    /// Returns the derivative of the polynomial.
    pub fn derivative(&self) -> Self {
        let mut res = self.clone();
        if self.data.len() == 0 {
            return res;
        }
        let _ = self.data.remove(0);
        let mut val: T = One::one();
        for data_i in res.data.iter_mut() {
            *data_i *= val.clone();
            val += One::one();
        }
        res
    }
}

impl<T: Clone + EuclideanDomain> Polynomial<T> {
    /// Get the content (gcd of the coefficients) of the polynomial
    pub fn cont(&self) -> T {
        if self.data.len() == 0 {
            return Zero::zero();
        }
        if self.data.len() == 1 {
            return self.data[0].clone();
        }
        let mut result = self.data[0].clone();
        for i in 1..self.data.len() {
            result = gcd(result, self.data[i].clone());
        }
        result
    }
}
