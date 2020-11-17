
use crate::prime::FPElt;
use nt_polynomial::*;
use nt_traits::*;
use num_traits::Zero;

#[derive(Clone, Debug, PartialEq, Eq)]
/// An element of the finite field F_{p^n}, for prime p and natural number n
pub struct FPnElt {
    /// A representative of the equivalence class of F_p[x] / <r(x)>
    val: Polynomial<FPElt>,
    /// A polynomial r(x) whose ideal is irreducible over F_p[x]
    r: Polynomial<FPElt>,
}

impl FPnElt {
    pub fn p(&self) -> u32 {
        self.r.data()[0].p
    }

    pub fn n(&self) -> usize {
        self.r.degree()
    }

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
        dbg!(&poly);
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
        // u = u.pow(p).modulus(r.clone());
        u = u.pow(p);
        u = u.modulus(r.clone());
        // Extra step
        // if (u.clone() - x.clone()).is_zero() {
        //     return false;
        // }
        dbg!(r.clone());
        dbg!(u.clone() - x.clone());
        let g = gcd(r.clone(), u.clone() - x.clone());
        if g.degree() != 0 || g.is_zero() {
            return false;
        }
    }
    true
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
