
use num_field_quad::*;
use polynomial::*;

use crate::mod_p::*;

use num_traits::{Zero, One};

#[derive(Clone, Debug, PartialEq)]
pub struct FiniteQuadraticMap {
    numer: Polynomial<ModPElt>,
    denom: Polynomial<ModPElt>,
}

impl FiniteQuadraticMap {
    pub fn derivative(&self) -> FiniteQuadraticMap {
        let mut f_prime = self.numer.clone();
        f_prime.derivative(); // Maybe I should have called this derive?
        let mut g_prime = self.denom.clone();
        g_prime.derivative();
        let f = &self.numer;
        let g = &self.denom;

        FiniteQuadraticMap {
            numer: g.clone() * f_prime - f.clone() * g_prime,
            denom: g.clone() * g.clone(),
        }
    }

    pub fn sigma_invariants(&self) -> [ModPElt; 3] {
        // Let F = f(z) - z, and G = w - f'(z) for indeterminant w
        // The resultant Res(F, G) is a polynomial in w with sigma_i
        // as coefficients (https://arxiv.org/pdf/1908.03184.pdf, page 9 bottom)
        // Terminology and variable names in this section stolen from Sage
        let df = self.derivative();
        dbg!(df.numer.pretty("z"));
        dbg!(df.denom.pretty("z"));
        let fix_poly = self.numer.clone() - self.denom.clone() * Polynomial::new(vec![Zero::zero(), One::one()]);
        let mult_poly_w = df.denom;
        let mult_poly_1 = -df.numer;
        let mut mult_poly_cont = vec![];
        for i in 0..std::cmp::max(mult_poly_1.data().len(), mult_poly_w.data().len()) {
            // Coefficient on z^i
            mult_poly_cont.push(
                Polynomial::new(vec![mult_poly_1.data().get(i).cloned().unwrap_or(Zero::zero()),
                                     mult_poly_w.data().get(i).cloned().unwrap_or(Zero::zero())]),
            );
        }
        let mult_poly: Polynomial<Polynomial<ModPElt>> = Polynomial::new(mult_poly_cont);
        let mut fix_poly_cont = vec![];
        for i in 0..fix_poly.data().len() {
            // Coefficient on z^i
            fix_poly_cont.push(
                Polynomial::new(vec![fix_poly.data().get(i).cloned().unwrap_or(Zero::zero())])
            );
        }
        let fix_poly: Polynomial<Polynomial<ModPElt>> = Polynomial::new(fix_poly_cont);
        dbg!(mult_poly.pretty("z"));
        // Compute the resultant
        let res = if fix_poly.degree() >= mult_poly.degree() {
            resultant(fix_poly, mult_poly)
        } else {
            resultant(mult_poly, fix_poly)
        };
        let mut sig = res.data().to_owned();
        let den = sig.pop().unwrap();
        assert!(sig.len() == 3);
        [
            -sig[2] / den,
            sig[1] / den,
            -sig[0] / den,
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sigma_invariants() {
        let numer = Polynomial::new(vec![ModPElt { val: 1, p: 13 }, ModPElt { val: 1, p: 13 }, ModPElt { val: 2, p: 13 }]);
        let denom = Polynomial::new(vec![ModPElt { val: 10, p: 13 }, ModPElt { val: 3, p: 13 }, ModPElt {val: 10, p: 13 }]);
        let phi = FiniteQuadraticMap {
            numer,
            denom,
        };

        dbg!(phi.sigma_invariants());
    }
}
