
use num_traits::*;
use std::ops::{Add, Mul, Div, Neg, Sub, AddAssign, SubAssign, MulAssign, DivAssign};
use alga::general::*;

use polynomial::EuclideanDomain;

pub fn mod_inverse(num: i64, prime: i64) -> i64 {
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
pub struct ModPElt {
    pub p: u32,
    pub val: i64,
}

impl std::fmt::Display for ModPElt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val)
    }
}

impl std::cmp::PartialEq for ModPElt {
    fn eq(&self, other: &Self) -> bool {
        self.val == other.val
    }
}

impl Eq for ModPElt {}

impl Add for ModPElt {
    type Output = ModPElt;

    fn add(self, other: ModPElt) -> ModPElt {
        if self.p == 0 && other.p == 0 { 
            return ModPElt {
                p: 0,
                val: self.val + other.val,
            };
        }
        let p = if self.p == 0 { other.p } else { self.p };
        // TODO: Maybe this should use checked_add
        ModPElt {
            p,
            val: (self.val + other.val).rem_euclid(p as i64)
        }
    }
}

impl AddAssign for ModPElt {
    fn add_assign(&mut self, other: ModPElt) {
        *self = *self + other;
    }
}

impl Sub for ModPElt {
    type Output = ModPElt;

    fn sub(self, other: ModPElt) -> ModPElt {
        if self.p == 0 && other.p == 0 { 
            return ModPElt {
                p: 0,
                val: self.val - other.val,
            };
        }
        let p = if self.p == 0 { other.p } else { self.p };
        ModPElt {
            p,
            val: (self.val - other.val).rem_euclid(p as i64)
        }
    }
}

impl SubAssign for ModPElt {
    fn sub_assign(&mut self, other: ModPElt) {
        *self = *self - other;
    }
}

impl Mul for ModPElt {
    type Output = ModPElt;

    fn mul(self, other: ModPElt) -> ModPElt {
        if self.p == 0 && other.p == 0 { 
            return ModPElt {
                p: 0,
                val: self.val * other.val,
            };
        }
        let p = if self.p == 0 { other.p } else { self.p };
        ModPElt {
            p,
            val: (self.val * other.val).rem_euclid(p as i64)
        }
    }
}

impl MulAssign for ModPElt {
    fn mul_assign(&mut self, other: ModPElt) {
        *self = *self * other;
    }
}

impl Div for ModPElt {
    type Output = ModPElt;

    fn div(self, other: ModPElt) -> ModPElt {
        self * (<Self as TwoSidedInverse<Multiplicative>>::two_sided_inverse(&other))
    }
}

impl DivAssign for ModPElt {
    fn div_assign(&mut self, other: ModPElt) {
        *self = *self / other;
    }
}

impl Neg for ModPElt {
    type Output = ModPElt;

    fn neg(self) -> ModPElt {
        if self.p == 0 {
            return ModPElt {
                p: self.p,
                val: -self.val,
            };
        }
        ModPElt {
            p: self.p,
            val: (-self.val).rem_euclid(self.p as i64)
        }
    }
}

impl One for ModPElt {
    fn one() -> Self {
        ModPElt {
            p: 0,
            val: 1
        }
    }
}

impl Zero for ModPElt {
    fn is_zero(&self) -> bool {
        self.val == 0
    }

    fn zero() -> Self {
        ModPElt {
            p: 0,
            val: 0,
        }
    }
}

impl AbstractMagma<Additive> for ModPElt {
    fn operate(&self, right: &Self) -> Self {
        *self + *right
    }
}

impl Identity<Additive> for ModPElt {
    fn identity() -> Self {
        ModPElt {
            p: 0,
            val: 0,
        }
    }
}

impl TwoSidedInverse<Additive> for ModPElt {
    fn two_sided_inverse(&self) -> Self {
        -*self
    }
}

impl AbstractQuasigroup<Additive> for ModPElt {}
impl AbstractLoop<Additive> for ModPElt {}
impl AbstractSemigroup<Additive> for ModPElt {}
impl AbstractMonoid<Additive> for ModPElt {}
impl AbstractGroup<Additive> for ModPElt {}
impl AbstractGroupAbelian<Additive> for ModPElt {}

impl AbstractMagma<Multiplicative> for ModPElt {
    fn operate(&self, right: &Self) -> Self {
        *self * *right
    }
}

impl Identity<Multiplicative> for ModPElt {
    fn identity() -> Self {
        ModPElt {
            p: 0,
            val: 1,
        }
    }
}

impl TwoSidedInverse<Multiplicative> for ModPElt {
    fn two_sided_inverse(&self) -> Self {
        ModPElt {
            p: self.p,
            val: mod_inverse(self.val, self.p as i64),
        }
    }
}

impl AbstractQuasigroup<Multiplicative> for ModPElt {}
impl AbstractLoop<Multiplicative> for ModPElt {}
impl AbstractSemigroup<Multiplicative> for ModPElt {}
impl AbstractMonoid<Multiplicative> for ModPElt {}
impl AbstractGroup<Multiplicative> for ModPElt {}
impl AbstractGroupAbelian<Multiplicative> for ModPElt {}

impl AbstractRing<Additive, Multiplicative> for ModPElt {}
impl AbstractRingCommutative<Additive, Multiplicative> for ModPElt {}
impl AbstractField<Additive, Multiplicative> for ModPElt {}


// Hacky
impl EuclideanDomain for ModPElt {
    fn modulus(self, other: Self) -> Self {
        let p = if self.p == 0 { other.p } else { self.p };
        ModPElt {
            val: 0,
            p
        }
    }

    fn gcd(self, other: Self) -> Self {
        let p = if self.p == 0 { other.p } else { self.p };
        ModPElt {
            val: 1,
            p
        }
    }
}
