//! Trait to be able to know at runtime if a generic scalar is an integer, a float
//! or a complex.

use num_complex::{Complex32, Complex64};

use std::{
    fmt,
    ops::{Add, Neg},
};

use crate::MulAcc;
/// the type for Pattern data, it's special which contains no data
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
pub struct Pattern;

impl Add for Pattern {
    type Output = Pattern;
    fn add(self, _other: Pattern) -> Pattern {
        Pattern
    }
}
impl Neg for Pattern {
    type Output = Pattern;
    fn neg(self) -> Pattern {
        Pattern
    }
}
impl num_traits::Zero for Pattern {
    fn zero() -> Pattern {
        Pattern
    }
    /// all patterns are zero
    fn is_zero(&self) -> bool {
        true
    }
}

impl MulAcc for Pattern {
    fn mul_acc(&mut self, _a: &Self, _b: &Self) {}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum NumKind {
    Integer,
    Float,
    Complex,
    Pattern,
}

impl fmt::Display for NumKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Integer => write!(f, "integer"),
            Self::Float => write!(f, "real"),
            Self::Complex => write!(f, "complex"),
            Self::Pattern => write!(f, "pattern"),
        }
    }
}

pub trait PrimitiveKind {
    /// Informs whether a generic primitive type contains an integer,
    /// a float or a complex
    fn num_kind() -> NumKind;
}
impl PrimitiveKind for Pattern {
    fn num_kind() -> NumKind {
        NumKind::Pattern
    }
}

macro_rules! integer_prim_kind_impl {
    ($prim: ty) => {
        impl PrimitiveKind for $prim {
            fn num_kind() -> NumKind {
                NumKind::Integer
            }
        }
    };
}

integer_prim_kind_impl!(i8);
integer_prim_kind_impl!(u8);
integer_prim_kind_impl!(i16);
integer_prim_kind_impl!(u16);
integer_prim_kind_impl!(i32);
integer_prim_kind_impl!(u32);
integer_prim_kind_impl!(i64);
integer_prim_kind_impl!(u64);
integer_prim_kind_impl!(isize);
integer_prim_kind_impl!(usize);

macro_rules! float_prim_kind_impl {
    ($prim: ty) => {
        impl PrimitiveKind for $prim {
            fn num_kind() -> NumKind {
                NumKind::Float
            }
        }
    };
}

float_prim_kind_impl!(f32);
float_prim_kind_impl!(f64);

macro_rules! complex_prim_kind_impl {
    ($prim: ty) => {
        impl PrimitiveKind for $prim {
            fn num_kind() -> NumKind {
                NumKind::Complex
            }
        }
    };
}

complex_prim_kind_impl!(Complex32);
complex_prim_kind_impl!(Complex64);

#[cfg(test)]
mod tests {
    use num_traits::Zero;

    use super::*;

    #[test]
    fn test_pattern() {
        assert_eq!(Pattern::zero(), Pattern);
        assert_eq!(Pattern.is_zero(), true);
        let mut pattern = Pattern;
        pattern.set_zero();
        assert_eq!(pattern, Pattern);

        assert_eq!(Pattern + Pattern, Pattern);
        assert_eq!(-Pattern, Pattern);
        pattern.mul_acc(&Pattern, &Pattern);
        assert_eq!(pattern, Pattern);
    }
}
