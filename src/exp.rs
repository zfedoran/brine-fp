use super::consts::*;
use super::unsigned::UnsignedNumeric;
use super::signed::SignedNumeric;

// Modified from the original to support precise numbers instead of floats
// origin: FreeBSD /usr/src/lib/msun/src/e_exp.c */
// 
// ====================================================
// Copyright (C) 2004 by Sun Microsystems, Inc. All rights reserved.
// 
// Permission to use, copy, modify, and distribute this
// software is freely granted, provided that this notice
// is preserved.
// ====================================================
// 
// exp(x)
// Returns the exponential of x.
// 
// Method
//   1. Argument reduction:
//      Reduce x to an r so that |r| <= 0.5*ln2 ~ 0.34658.
//      Given x, find r and integer k such that
// 
//               x = k*ln2 + r,  |r| <= 0.5*ln2.
// 
//      Here r will be represented as r = hi-lo for better
//      accuracy.
// 
//   2. Approximation of exp(r) by a special rational function on
//      the interval [0,0.34658]:
//      Write
//          R(r**2) = r*(exp(r)+1)/(exp(r)-1) = 2 + r*r/6 - r**4/360 + ...
//      We use a special Remez algorithm on [0,0.34658] to generate
//      a polynomial of degree 5 to approximate R. The maximum error
//      of this polynomial approximation is bounded by 2**-59. In
//      other words,
//          R(z) ~ 2.0 + P1*z + P2*z**2 + P3*z**3 + P4*z**4 + P5*z**5
//      (where z=r*r, and the values of P1 to P5 are listed below)
//      and
//          |                  5          |     -59
//          | 2.0+P1*z+...+P5*z   -  R(z) | <= 2
//          |                             |
//      The computation of exp(r) thus becomes
//                              2*r
//              exp(r) = 1 + ----------
//                            R(r) - r
//                                 r*c(r)
//                     = 1 + r + ----------- (for better accuracy)
//                                2 - c(r)
//      where
//                              2       4             10
//              c(r) = r - (P1*r  + P2*r  + ... + P5*r   ).
// 
//   3. Scale back to obtain exp(x):
//      From step 1, we have
//         exp(x) = 2^k * exp(r)
// 
// Special cases:
//      exp(INF) is INF, exp(NaN) is NaN;
//      exp(-INF) is 0, and
//      for finite argument, only exp(0)=1 is exact.
// 
// Accuracy:
//      according to an error analysis, the error is always less than
//      1 ulp (unit in the last place).
// 
// Misc. info.
//      For IEEE double
//          if x >  709.782712893383973096 then exp(x) overflows
//          if x < -745.133219101941108420 then exp(x) underflows

impl SignedNumeric {

    /// Calculate the exponential of `x`, that is, *e* raised to the power `x`
    /// (where *e* is the base of the natural system of logarithms, approximately 2.71828).
    /// Note that precision can start to get inaccurate for larger numbers (> 20).
    pub fn exp(&self) -> Option<UnsignedNumeric> {
        let hi: Self;
        let lo: Self;
        let k: Self;
        let x: Self;

        // argument reduction
        // if |x| > 0.5 ln2
        if self.value.greater_than(&HALFLN2) {
            // if |x| >= 1.5 ln2
            if self.value.greater_than_or_equal(&THREEHALFLN2) {
                k = INVLN2
                    .signed()
                    .checked_mul(self)?
                    .checked_add(&Self {
                        value: HALF,
                        is_negative: self.is_negative,
                    })?
                    .floor()?;

                // A K larger than this value will cause less than 9 decimals of precision
                // if k.value.to_imprecise()? > 29 {
                //   return None
                // }
            } else {
                k = Self {
                    value: UnsignedNumeric::one(),
                    is_negative: self.is_negative,
                }
            }
            hi = self.checked_sub(
                &k.checked_mul(&LN2HI.signed())?
                    .checked_div(&LN2HI_SCALE.signed())?,
            )?;

            lo = k
                .checked_mul(&LN2LO.signed())?
                .checked_div(&LN2LO_SCALE.signed())?;
            x = hi.checked_sub(&lo)?
        } else {
            x = self.clone();
            k = UnsignedNumeric::zero().signed();
            hi = self.clone();
            lo = UnsignedNumeric::zero().signed()
        }

        // x is now in primary range
        let xx = x.checked_mul(&x)?;
        // c = x - xx * (P1 + xx * (P2 + xx * (P3 + xx * (P4 + xx * P5))));
        let p4p5 = P4.checked_add(&xx.checked_mul(&P5)?)?;
        let p3p4p5 = P3.checked_add(&xx.checked_mul(&p4p5)?)?;
        let p2p3p4p5 = P2.checked_add(&xx.checked_mul(&p3p4p5)?)?;
        let p1p2p3p4p5 = P1.checked_add(&xx.checked_mul(&p2p3p4p5)?)?;
        let c = x.checked_sub(&p1p2p3p4p5.checked_mul(&xx)?)?;

        // y = 1. + (x * c / (2. - c) - lo + hi);
        let y = ONE_PREC.signed().checked_add(
            &x.checked_mul(&c)?
                .checked_div(&TWO_PREC.signed().checked_sub(&c)?)?
                .checked_sub(&lo)?
                .checked_add(&hi)?,
        )?;

        if k.value.eq(&UnsignedNumeric::zero()) {
            Some(y.value)
        } else {
            let bits = k.value.to_imprecise()?;

            if k.is_negative {
                Some(UnsignedNumeric {
                    value: y.value.value >> bits,
                })
            } else {
                Some(UnsignedNumeric {
                    value: y.value.value << bits,
                })
            }
        }
    }

    /// Returns the square root of `self`, returning `None` if the number is negative.
    pub fn sqrt(&self) -> Option<Self> {
        if self.is_negative {
            return None;
        }
        self.value.sqrt().map(|v| Self { value: v, is_negative: false })
    }
}

impl UnsignedNumeric {

    /// Frexp breaks f into a normalized fraction and an integral power of two. It returns frac and
    /// exp satisfying f == frac × 2**exp, with the absolute value of frac in the interval [½, 1).
    ///
    /// Special cases are:
    ///	Frexp(±0) = ±0, 0
    ///	Frexp(±Inf) = ±Inf, 0
    ///	Frexp(NaN) = NaN, 0
    pub fn frexp(&self) -> Option<(Self, i64)> {
        if self.eq(&ZERO_PREC) {
            Some((ZERO_PREC.clone(), 0))
        } else if self.less_than(&ONE_PREC) {
            let first_leading = self.value.0[0].leading_zeros();
            let one_leading = ONE_PREC.value.0[0].leading_zeros();
            let bits = i64::from(first_leading.checked_sub(one_leading).unwrap());
            let frac = UnsignedNumeric {
                value: self.value << bits,
            };
            if frac.less_than(&HALF) {
                Some((frac.checked_mul(&TWO_PREC).unwrap(), -bits - 1))
            } else {
                Some((frac, -bits))
            }
        } else {
            let bits = 128_i64.checked_sub(i64::from(self.to_imprecise()?.leading_zeros()))?;
            let frac = UnsignedNumeric {
                value: self.value >> bits,
            };
            if frac.less_than(&HALF) {
                Some((frac.checked_mul(&TWO_PREC).unwrap(), bits - 1))
            } else {
                Some((frac, bits))
            }
        }
    }

    /// Raises `self` to the power of `exp`, returning the result as a new `UnsignedNumeric`.
    /// Returns `None` if the operation would overflow or if `self` is zero.
    ///
    /// b = pow/frac
    /// y = a^b
    /// ln (y) = bln (a)
    /// y = e^(b ln (a))
    pub fn pow(&self, exp: &Self) -> Option<Self> {
        if self.eq(&ZERO_PREC) {
            return Some(ZERO_PREC.clone());
        }

        let lg = self.log()?;
        let x = exp.signed().checked_mul(&lg)?;
        x.exp()
    }

    /// Returns the square root of `self`
    pub fn sqrt(&self) -> Option<Self> {
        self.pow(&HALF)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::InnerUint;

    fn frexp_recombine(frac: UnsignedNumeric, exp: i64) -> UnsignedNumeric {
        let shifted = if exp >= 0 {
            UnsignedNumeric {
                value: frac.value << (exp as usize),
            }
        } else {
            UnsignedNumeric {
                value: frac.value >> ((-exp) as usize),
            }
        };
        shifted
    }

    #[test]
    fn test_signed_exp() {
        let precision = InnerUint::from(1_000_000_000_u128); // correct to at least 9 decimal places

        let half = UnsignedNumeric { value: half() }.signed();
        assert!(half.exp().unwrap().almost_eq(
            &UnsignedNumeric::new(16487212707001282)
                .unwrap()
                .checked_div(&UnsignedNumeric::new(10000000000000000).unwrap())
                .unwrap(),
            precision
        ));

        let three_half = UnsignedNumeric::new(15)
            .unwrap()
            .checked_div(&UnsignedNumeric::new(10).unwrap())
            .unwrap()
            .signed();
        assert!(three_half.exp().unwrap().almost_eq(
            &UnsignedNumeric::new(44816890703380645)
                .unwrap()
                .checked_div(&UnsignedNumeric::new(10000000000000000).unwrap())
                .unwrap(),
            precision
        ));

        let point_one = UnsignedNumeric::new(1)
            .unwrap()
            .checked_div(&UnsignedNumeric::new(10).unwrap())
            .unwrap()
            .signed();
        assert!(point_one.exp().unwrap().almost_eq(
            &UnsignedNumeric::new(11051709180756477)
                .unwrap()
                .checked_div(&UnsignedNumeric::new(10000000000000000).unwrap())
                .unwrap(),
            precision
        ));

        let negative = UnsignedNumeric::new(55)
            .unwrap()
            .checked_div(&UnsignedNumeric::new(100).unwrap())
            .unwrap()
            .signed()
            .negate();
        assert!(negative.exp().unwrap().almost_eq(
            &UnsignedNumeric::new(5769498103804866)
                .unwrap()
                .checked_div(&UnsignedNumeric::new(10000000000000000).unwrap())
                .unwrap(),
            precision
        ));

        let test = UnsignedNumeric::new(19).unwrap().signed();
        assert!(test.exp().unwrap().almost_eq(
            &UnsignedNumeric::new(178482300963187260)
                .unwrap()
                .checked_div(&UnsignedNumeric::new(1000000000).unwrap())
                .unwrap(),
            precision
        ));
    }

    #[test]
    fn test_pow() {
        let precision = InnerUint::from(5_000_000_000_000_u128); // correct to at least 12 decimal places
        let test = UnsignedNumeric::new(8).unwrap();
        let sqrt = test.pow(&HALF).unwrap();
        let expected = UnsignedNumeric::new(28284271247461903)
            .unwrap()
            .checked_div(&UnsignedNumeric::new(10000000000000000).unwrap())
            .unwrap();
        assert!(sqrt.almost_eq(&expected, precision));

        let test2 = UnsignedNumeric::new(55)
            .unwrap()
            .checked_div(&UnsignedNumeric::new(100).unwrap())
            .unwrap();
        let squared = test2.pow(&TWO_PREC).unwrap();
        let expected = UnsignedNumeric::new(3025)
            .unwrap()
            .checked_div(&UnsignedNumeric::new(10000).unwrap())
            .unwrap();
        assert!(squared.almost_eq(&expected, precision));
    }

    #[test]
    fn test_sqrt() {
        let precision = InnerUint::from(5_000_000_000_000_u128); // correct to at least 12 decimal places
        let test = UnsignedNumeric::new(12).unwrap();
        let sqrt = test.sqrt().unwrap();
        let expected = UnsignedNumeric::new(34641016151377544)
            .unwrap()
            .checked_div(&UnsignedNumeric::new(10000000000000000).unwrap())
            .unwrap();
        assert!(sqrt.almost_eq(&expected, precision));
    }

    #[test]
    pub fn test_signed_sqrt() {
        let precision = InnerUint::from(5_000_000_000_000_u128); // correct to at least 12 decimal places
        let test = SignedNumeric {
            value: UnsignedNumeric::new(8).unwrap(),
            is_negative: false,
        };
        let sqrt = test.sqrt().unwrap();
        let expected = UnsignedNumeric::new(28284271247461903)
            .unwrap()
            .checked_div(&UnsignedNumeric::new(10000000000000000).unwrap())
            .unwrap();
        assert!(sqrt.value.almost_eq(&expected, precision));

        let neg_test = SignedNumeric {
            value: UnsignedNumeric::new(8).unwrap(),
            is_negative: true,
        };
        assert!(neg_test.sqrt().is_none());
    }

    #[test]
    fn test_exp_zero() {
        let zero = UnsignedNumeric::zero().signed();
        let result = zero.exp().unwrap();
        assert_eq!(result, UnsignedNumeric::one());
    }

    #[test]
    fn test_exp_small_negative() {
        let x = UnsignedNumeric::new(1)
            .unwrap()
            .checked_div(&UnsignedNumeric::new(1000).unwrap())
            .unwrap()
            .signed()
            .negate();
        let result = x.exp().unwrap();

        // e^-0.001 ≈ 0.999000499833375 (scaled: 999000499833375000)
        let expected = UnsignedNumeric::from_scaled_u128(999_000_499_833_375_000);
        assert!(
            result.almost_eq(&expected, InnerUint::from(10_000_000)),
            "got: {} expected: {}",
            result.to_string(),
            expected.to_string()
        );
    }

    #[test]
    fn test_exp_large_positive() {
        let x = UnsignedNumeric::new(10).unwrap().signed(); // e^10 ≈ 22026.4657948067
        let result = x.exp().unwrap();

        // Correctly scaled expected value: e^10 * 1e18
        let expected = UnsignedNumeric::from_scaled_u128(22_026_465_794_806_700_000_000);
        assert!(
            result.almost_eq(&expected, InnerUint::from(1_000_000_000_000_u64)),
            "got: {} expected: {}",
            result.to_string(),
            expected.to_string()
        );
    }

    #[test]
    fn test_exp_large_negative() {
        let x = UnsignedNumeric::new(10).unwrap().signed().negate(); // e^-10 ≈ 0.00004539992
        let result = x.exp().unwrap();

        let expected = UnsignedNumeric::from_scaled_u128(45_399_920_000_000); // scaled by 10^18
        assert!(
            result.almost_eq(&expected, InnerUint::from(1_000_000_000)),
            "got: {} expected: {}",
            result.to_string(),
            expected.to_string()
        );
    }

    #[test]
    fn test_frexp_zero() {
        let zero = UnsignedNumeric::zero();
        let (frac, exp) = zero.frexp().unwrap();
        assert_eq!(frac, zero);
        assert_eq!(exp, 0);
    }

    #[test]
    fn test_frexp_one() {
        let one = UnsignedNumeric::one();
        let (frac, exp) = one.frexp().unwrap();
        // Should return exactly 0.5 ≤ frac < 1, and 1.0 == frac × 2^exp
        let recombined = frexp_recombine(frac.clone(), exp);
        assert!(
            recombined.almost_eq(&one, InnerUint::from(1_000_000_000)),
            "Expected: {}, Got: {} × 2^{} = {}",
            one.to_string(),
            frac.to_string(),
            exp,
            recombined.to_string()
        );
        assert!(frac.greater_than_or_equal(&HALF));
        assert!(frac.less_than(&ONE_PREC));
    }

    #[test]
    fn test_frexp_two() {
        let two = UnsignedNumeric::new(2).unwrap();
        let (frac, exp) = two.frexp().unwrap();
        let recombined = frexp_recombine(frac.clone(), exp);
        assert!(
            recombined.almost_eq(&two, InnerUint::from(1_000_000_000)),
            "Expected: {}, Got: {} × 2^{} = {}",
            two.to_string(),
            frac.to_string(),
            exp,
            recombined.to_string()
        );
        assert!(frac.greater_than_or_equal(&HALF));
        assert!(frac.less_than(&ONE_PREC));
    }

    #[test]
    fn test_frexp_fractional() {
        let val = UnsignedNumeric::new(3).unwrap()
            .checked_div(&UnsignedNumeric::new(4).unwrap()) // 0.75
            .unwrap();
        let (frac, exp) = val.frexp().unwrap();
        let recombined = frexp_recombine(frac.clone(), exp);

        assert!(
            recombined.almost_eq(&val, InnerUint::from(1_000_000_000)),
            "Expected: {}, Got: {} × 2^{} = {}",
            val.to_string(),
            frac.to_string(),
            exp,
            recombined.to_string()
        );
        assert!(frac.greater_than_or_equal(&HALF));
        assert!(frac.less_than(&ONE_PREC));
    }

    #[test]
    fn test_frexp_large_value() {
        let val = UnsignedNumeric {
            value: InnerUint([0, 0, 1]), // 2^128 scaled fixed-point
        };
        let (frac, exp) = val.frexp().unwrap();
        let recombined = frexp_recombine(frac.clone(), exp);

        assert!(
            recombined.almost_eq(&val, InnerUint::from(10_000_000_000_u64)),
            "Expected: {}, Got: {} × 2^{} = {}",
            val.to_string(),
            frac.to_string(),
            exp,
            recombined.to_string()
        );
    }
}
