use super::consts::*;
use super::unsigned::UnsignedNumeric;
use super::signed::SignedNumeric;

// Modified from the original to support precise numbers instead of floats
// The original C code, the long comment, and the constants
// below are from FreeBSD's /usr/src/lib/msun/src/e_log.c
// and came with this notice. The go code is a simpler
// version of the original C.
//
// ====================================================
// Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
//
// Developed at SunPro, a Sun Microsystems, Inc. business.
// Permission to use, copy, modify, and distribute this
// software is freely granted, provided that this notice
// is preserved.
// ====================================================
//
// __ieee754_log(x)
// Return the logarithm of x
//
// Method :
//   1. Argument Reduction: find k and f such that
//			x = 2**k * (1+f),
//	   where  sqrt(2)/2 < 1+f < sqrt(2) .
//
//   2. Approximation of log(1+f).
//	Let s = f/(2+f) ; based on log(1+f) = log(1+s) - log(1-s)
//		 = 2s + 2/3 s**3 + 2/5 s**5 + .....,
//	     	 = 2s + s*R
//      We use a special Reme algorithm on [0,0.1716] to generate
//	a polynomial of degree 14 to approximate R.  The maximum error
//	of this polynomial approximation is bounded by 2**-58.45. In
//	other words,
//		        2      4      6      8      10      12      14
//	    R(z) ~ L1*s +L2*s +L3*s +L4*s +L5*s  +L6*s  +L7*s
//	(the values of L1 to L7 are listed in the program) and
//	    |      2          14          |     -58.45
//	    | L1*s +...+L7*s    -  R(z) | <= 2
//	    |                             |
//	Note that 2s = f - s*f = f - hfsq + s*hfsq, where hfsq = f*f/2.
//	In order to guarantee error in log below 1ulp, we compute log by
//		log(1+f) = f - s*(f - R)		(if f is not too large)
//		log(1+f) = f - (hfsq - s*(hfsq+R)).	(better accuracy)
//
//	3. Finally,  log(x) = k*Ln2 + log(1+f).
//			    = k*Ln2_hi+(f-(hfsq-(s*(hfsq+R)+k*Ln2_lo)))
//	   Here Ln2 is split into two floating point number:
//			Ln2_hi + Ln2_lo,
//	   where n*Ln2_hi is always exact for |n| < 2000.
//
// Special cases:
//	log(x) is NaN with signal if x < 0 (including -INF) ;
//	log(+INF) is +INF; log(0) is -INF with signal;
//	log(NaN) is that NaN with no signal.
//
// Accuracy:
//	according to an error analysis, the error is always less than
//	1 ulp (unit in the last place).
//
// Constants:
// The hexadecimal values are the intended ones for the following
// constants. The decimal values may be used, provided that the
// compiler will convert from decimal to binary accurately enough
// to produce the hexadecimal values shown.
// Frexp breaks f into a normalized fraction
// and an integral power of two.
// It returns frac and exp satisfying f == frac × 2**exp,
// with the absolute value of frac in the interval [½, 1).


impl UnsignedNumeric {

    /// Log returns the natural logarithm of x.
    ///
    /// Special cases are:
    ///	Log(+Inf) = +Inf
    ///	Log(0) = -Inf
    ///	Log(x < 0) = NaN
    pub fn log(&self) -> Option<SignedNumeric> {
        if self.eq(&ZERO_PREC) {
            return None;
        }

        if self.eq(&ONE_PREC) {
            return Some(SignedNumeric {
                value: ZERO_PREC.clone(),
                is_negative: false,
            });
        }

        let (f1_init, ki_init) = self.frexp()?;

        let (f1, ki) = if f1_init.less_than(&SQRT2OVERTWO) {
            let new_f1 = f1_init.checked_mul(&TWO_PREC)?;
            let new_k1 = ki_init.checked_sub(1)?;
            (new_f1, new_k1)
        } else {
            (f1_init, ki_init)
        };

        let f = f1.signed().checked_sub(&UnsignedNumeric::one().signed())?;

        let s_divisor = UnsignedNumeric { value: two() }.signed().checked_add(&f)?;
        let s = &f.checked_div(&s_divisor)?;
        let s2 = s.checked_mul(s)?.value;
        let s4 = s2.checked_mul(&s2)?;
        // s2 * (L1 + s4*(L3+s4*(L5+s4*L7)))
        let t1 = s2.checked_mul(&L1.checked_add(&s4.checked_mul(
            &L3.checked_add(&s4.checked_mul(&L5.checked_add(&s4.checked_mul(&L7)?)?)?)?
        )?)?)?;

        // s4 * (L2 + s4*(L4+s4*L6))
        let t2 = s4.checked_mul(
            &L2.checked_add(&s4.checked_mul(&L4.checked_add(&s4.checked_mul(&L6)?)?)?)?,
        )?;

        let r = t1.checked_add(&t2)?;
        let hfsq = f
            .checked_mul(&f)?
            .checked_div(&UnsignedNumeric { value: two() }.signed())?;
        let k = SignedNumeric {
            value: UnsignedNumeric::new(u128::try_from(ki.abs()).ok()?),
            is_negative: ki < 0,
        };

        // k*Ln2Hi - ((hfsq - (s*(hfsq+R) + k*Ln2Lo)) - f)
        let kl2hi = k
            .checked_mul(&LN2HI.signed())?
            .checked_div(&LN2HI_SCALE.signed())?;
        let shfsqr = s.checked_mul(&hfsq.checked_add(&r.signed())?)?;
        let kl2lo = k
            .checked_mul(&LN2LO.signed())?
            .checked_div(&LN2LO_SCALE.signed())?;

        let shfsqr_kl2lo = shfsqr.checked_add(&kl2lo)?;
        let hfsq_shfsqr_kl2lo = hfsq.checked_sub(&shfsqr_kl2lo)?;
        let f_hfsq_shfsqr_kl2lo = hfsq_shfsqr_kl2lo.checked_sub(&f)?;

        kl2hi.checked_sub(&f_hfsq_shfsqr_kl2lo)
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::InnerUint;

    #[test]
    fn test_log() {
        let precision = InnerUint::from(5_000_000_000_u128); // correct to at least 9 decimal places

        let test = UnsignedNumeric::new(9);
        let log = test.log().unwrap().value;
        let expected = UnsignedNumeric::new(21972245773362196)
            .checked_div(&UnsignedNumeric::new(10000000000000000))
            .unwrap();
        assert!(log.almost_eq(&expected, precision));

        let test2 = UnsignedNumeric::new(2);
        assert!(test2.log().unwrap().value.almost_eq(
            &UnsignedNumeric::new(6931471805599453)
                .checked_div(&UnsignedNumeric::new(10000000000000000))
                .unwrap(),
            precision
        ));

        let test3 = &UnsignedNumeric::new(12)
            .checked_div(&UnsignedNumeric::new(10))
            .unwrap();
        assert!(test3.log().unwrap().value.almost_eq(
            &UnsignedNumeric::new(1823215567939546)
                .checked_div(&UnsignedNumeric::new(10000000000000000))
                .unwrap(),
            precision
        ));

        let test5 = &UnsignedNumeric::new(15)
            .checked_div(&UnsignedNumeric::new(10))
            .unwrap();
        assert!(test5.log().unwrap().value.almost_eq(
            &UnsignedNumeric::new(4054651081081644)
                .checked_div(&UnsignedNumeric::new(10000000000000000))
                .unwrap(),
            precision
        ));

        let test6 = UnsignedNumeric::new(4)
            .checked_div(&UnsignedNumeric::new(1000000))
            .unwrap();
        assert!(test6.log().unwrap().value.almost_eq(
            &UnsignedNumeric::new(12429216196844383)
                .checked_div(&UnsignedNumeric::new(1000000000000000))
                .unwrap(),
            precision
        ));
    }
}
