
use num_field_quad::*;

pub fn mod_inverse(num: i16, prime: i16) -> i16 {
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

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum ProjectivePoint {
    Finite(i16),
    Infinite,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct FiniteQuadraticMap {
    p: u16,
    numer: QuadPoly<i16>,
    denom: QuadPoly<i16>,
}

impl FiniteQuadraticMap {
    pub fn find_fixed_points(&self) -> Vec<ProjectivePoint> {
        let mut fixed_pts = vec![];

        for i in 0..(self.p as i16) {
            if self.eval(i) == i {
                fixed_pts.push(ProjectivePoint::Finite(i));
            }
        }

        if self.denom.degree() == 0 {
            fixed_pts.push(ProjectivePoint::Infinite);
        }
    
        fixed_pts
    }

    pub fn eval(&self, pt: i16) -> i16 {
        let a = self.numer.a;
        let b = self.numer.b;
        let c = self.numer.c;
        let d = self.denom.a;
        let e = self.denom.b;
        let f = self.denom.c;
        let f_pt = a * pt * pt + b * pt + c;
        let f_pt = f_pt.rem_euclid(self.p as i16);
        let g_pt = d * pt * pt + e * pt + f;
        let g_pt = g_pt.rem_euclid(self.p as i16);
        (f_pt * mod_inverse(g_pt, self.p as i16)).rem_euclid(self.p as i16)
    }

    pub fn eval_derivative(&self, pt: i16) -> i16 {
        let a = self.numer.a;
        let b = self.numer.b;
        let c = self.numer.c;
        let d = self.denom.a;
        let e = self.denom.b;
        let f = self.denom.c;
        let f_pt = a * pt * pt + b * pt + c;
        let f_pt = f_pt.rem_euclid(self.p as i16);
        let g_pt = d * pt * pt + e * pt + f;
        let g_pt = g_pt.rem_euclid(self.p as i16);
        let f_prime_pt = 2 * a * pt + b;
        let f_prime_pt = f_prime_pt.rem_euclid(self.p as i16);
        let g_prime_pt = 2 * d * pt + e;
        let g_prime_pt = g_prime_pt.rem_euclid(self.p as i16);
        // Quotient rule (assume we're f/g)
        ((g_pt * f_prime_pt - f_pt * g_prime_pt) * mod_inverse((g_pt * g_pt).rem_euclid(self.p as i16), self.p as i16))
            .rem_euclid(self.p as i16)
    }

    pub fn fixed_point_multiplier(&self, fixed_pt: ProjectivePoint) -> i16 {
        let val = match fixed_pt {
            ProjectivePoint::Infinite => {
                // Infinity is a fixed point; we are a polynomial.
                return 0;
            },
            ProjectivePoint::Finite(x) => x,
        };
        // f'(fixed_pt) % p
        self.eval_derivative(val).rem_euclid(self.p as i16)
    }

    pub fn sigma_invariants(&self) -> [i16; 2] {
        // THIS DOESNT WORK BECAUSE I NEED TO BE WORKING OVER K bar TO
        // FIND THE 3 FIXED POINTS UGH
        let fixed_pts = self.find_fixed_points();
        if fixed_pts.len() != 3 {
            panic!("Called sigma_invariants on a degree n < 2 map");
        }
        let lambda_1 = self.fixed_point_multiplier(fixed_pts[0]);
        let lambda_2 = self.fixed_point_multiplier(fixed_pts[1]);
        let lambda_3 = self.fixed_point_multiplier(fixed_pts[2]);
        [
            (lambda_1 + lambda_2 + lambda_3).rem_euclid(self.p as i16),
            (lambda_1 * lambda_2 + lambda_1 * lambda_3 + lambda_2 * lambda_3).rem_euclid(self.p as i16)
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sigma_invariants() {
        let numer = QuadPoly {
            a: 2,
            b: 1,
            c: 1,
        };
        let denom = QuadPoly {
            a: 10,
            b: 3,
            c: 10,
        };

        let phi = FiniteQuadraticMap {
            numer,
            denom,
            p: 11,
        };

        dbg!(phi.sigma_invariants());
    }
}
