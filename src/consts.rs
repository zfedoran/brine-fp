use super::InnerUint;
use super::unsigned::UnsignedNumeric;
use super::signed::SignedNumeric;

// UnsignedNumeric constants

/// The representation of the number one as a precise number as 10^18
pub const ONE: u128 = 1_000_000_000_000_000_000;

pub static ONE_PREC: UnsignedNumeric = UnsignedNumeric { value: one() };
pub static ZERO_PREC: UnsignedNumeric = UnsignedNumeric { value: zero() };
pub static TWO_PREC: UnsignedNumeric = UnsignedNumeric { value: two() };

/// Zero value in fixed-point format.
#[inline]
pub const fn zero() -> InnerUint {
    InnerUint([0, 0, 0])
}

/// Returns the internal representation of 1.0 in fixed-point format.
#[inline]
pub const fn one() -> InnerUint {
    InnerUint([ONE as u64, 0, 0])
}

/// Returns the internal representation of 2.0 in fixed-point format.
#[inline]
pub const fn two() -> InnerUint {
    InnerUint([2 * ONE as u64, 0, 0])
}

/// Fixed-point representation of 0.5 (HALF).
#[inline]
pub const fn half() -> InnerUint {
    InnerUint([500000000000000000_u64, 0, 0])
}
pub const HALF: UnsignedNumeric = UnsignedNumeric { value: half() };

/// High part of ln(2), used for logarithmic calculations. Stored as a fixed-point number.
#[inline]
pub const fn ln2hi() -> InnerUint {
    InnerUint([13974485815783726801_u64, 3_u64, 0])
}
pub const LN2HI: UnsignedNumeric = UnsignedNumeric { value: ln2hi() };

/// Scaled variant of ln2hi for internal use in higher-precision approximations.
#[inline]
pub const fn ln2hi_scale() -> InnerUint {
    InnerUint([7766279631452241920_u64, 5_u64, 0])
}
pub const LN2HI_SCALE: UnsignedNumeric = UnsignedNumeric { value: ln2hi_scale() };

/// Low part of ln(2). Very small value, stored separately for better precision.
#[inline]
pub const fn ln2lo() -> InnerUint {
    // Note that ln2lo is lower than our max precision, so we store both it and the thirty zeroes to scale by
    InnerUint([3405790746697269248_u64, 1034445385942222_u64, 0])
}
pub const LN2LO: UnsignedNumeric = UnsignedNumeric { value: ln2lo() };

/// Scaled low part of ln(2), for use in precision-sensitive computations.
#[inline]
pub const fn ln2lo_scale() -> InnerUint {
    InnerUint([80237960548581376_u64, 10841254275107988496_u64, 293873_u64])
}
pub const LN2LO_SCALE: UnsignedNumeric = UnsignedNumeric { value: ln2lo_scale() };

/// Constant for 1/2 * ln(2), useful in logarithmic calculations.
#[inline]
pub const fn halfln2() -> InnerUint {
    InnerUint([346573590279972640_u64, 0_u64, 0_u64])
}
pub const HALFLN2: UnsignedNumeric = UnsignedNumeric { value: halfln2() };

/// Constant for 3/2 * ln(2), useful in logarithmic calculations.
#[inline]
pub const fn threehalfln2() -> InnerUint {
    InnerUint([1039720770839917900_u64, 0_u64, 0_u64])
}
pub const THREEHALFLN2: UnsignedNumeric = UnsignedNumeric {
    value: threehalfln2(),
};

/// Constant for 1/ln(2), useful in logarithmic calculations.
#[inline]
pub const fn invln2() -> InnerUint {
    InnerUint([1442695040888963387_u64, 0_u64, 0_u64])
}
pub const INVLN2: UnsignedNumeric = UnsignedNumeric { value: invln2() };

/// Constant for sqrt(2)/2, useful in trig/log calculations.
#[inline]
pub const fn sqrt2overtwo() -> InnerUint {
    InnerUint([707106781186547600_u64, 0, 0])
}
pub const SQRT2OVERTWO: UnsignedNumeric = UnsignedNumeric { value: sqrt2overtwo() };

// Remez constants for logarithmic approximation

#[inline]
pub const fn l1() -> InnerUint {
    InnerUint([666666666666673513_u64, 0_u64, 0_u64])
}
pub const L1: UnsignedNumeric = UnsignedNumeric { value: l1() };

#[inline]
pub const fn l2() -> InnerUint {
    InnerUint([399999999994094190_u64, 0_u64, 0_u64])
}
pub const L2: UnsignedNumeric = UnsignedNumeric { value: l2() };

#[inline]
pub const fn l3() -> InnerUint {
    InnerUint([285714287436623914_u64, 0_u64, 0_u64])
}
pub const L3: UnsignedNumeric = UnsignedNumeric { value: l3() };

#[inline]
pub const fn l4() -> InnerUint {
    InnerUint([222221984321497839_u64, 0_u64, 0_u64])
}
pub const L4: UnsignedNumeric = UnsignedNumeric { value: l4() };

#[inline]
pub const fn l5() -> InnerUint {
    InnerUint([181835721616180501_u64, 0_u64, 0_u64])
}
pub const L5: UnsignedNumeric = UnsignedNumeric { value: l5() };

pub const fn l6() -> InnerUint {
    InnerUint([153138376992093733_u64, 0_u64, 0_u64])
}
pub const L6: UnsignedNumeric = UnsignedNumeric { value: l6() };

#[inline]
pub const fn l7() -> InnerUint {
    InnerUint([147981986051165859_u64, 0_u64, 0_u64])
}
pub const L7: UnsignedNumeric = UnsignedNumeric { value: l7() };

// Remez constants for exp approximation

#[inline]
pub const fn p1() -> InnerUint {
    InnerUint([166666666666666019_u64, 0_u64, 0_u64])
}
pub const P1: SignedNumeric = SignedNumeric {
    value: UnsignedNumeric { value: p1() },
    is_negative: false,
};

#[inline]
pub const fn p2() -> InnerUint {
    InnerUint([2777777777701559_u64, 0_u64, 0_u64])
}
pub const P2: SignedNumeric = SignedNumeric {
    value: UnsignedNumeric { value: p2() },
    is_negative: true,
};

#[inline]
pub const fn p3() -> InnerUint {
    InnerUint([66137563214379_u64, 0_u64, 0_u64])
}
pub const P3: SignedNumeric = SignedNumeric {
    value: UnsignedNumeric { value: p3() },
    is_negative: false,
};

#[inline]
pub const fn p4() -> InnerUint {
    InnerUint([1653390220546_u64, 0_u64, 0_u64])
}
pub const P4: SignedNumeric = SignedNumeric {
    value: UnsignedNumeric { value: p4() },
    is_negative: true,
};

#[inline]
pub const fn p5() -> InnerUint {
    InnerUint([41381367970_u64, 0_u64, 0_u64])
}
pub const P5: SignedNumeric = SignedNumeric {
    value: UnsignedNumeric { value: p5() },
    is_negative: false,
};

