use super::unsigned::UnsignedNumeric;

// Based on the following implementations:
// https://github.com/solana-labs/solana-program-library/blob/v2.0/libraries/math/src/precise_number.rs
// https://github.com/StrataFoundation/strata/blob/master/programs/spl-token-bonding/src/signed_precise_number.rs

/// A `SignedNumeric` represents a signed 192-bit fixed-point number with 18 decimal places of precision.
///
/// This struct extends [`UnsignedNumeric`] by adding a `bool` flag to indicate whether the value is negative,
/// enabling full support for signed decimal arithmetic.
///
/// ### Internal Representation
/// - The magnitude is stored as a [`UnsignedNumeric`], which wraps a [`InnerUint`] representing a 192-bit unsigned integer scaled by 10¹⁸.
/// - The `is_negative` flag determines the sign of the number.
///
/// ### Interpretation
/// The real-world value of a `SignedNumeric` is:
/// ```text
/// value = (is_negative ? -1 : 1) × (magnitude / 10^18)
/// ```
///
/// ### Examples:
/// - `value = UnsignedNumeric::from_u192([1_000_000_000_000_000_000, 0, 0]), is_negative = false` → 1.0
/// - `value = UnsignedNumeric::from_u192([5_000_000_000_000_000_000, 0, 0]), is_negative = true`  → -5.0
///
/// This format is useful for financial and scientific applications where both precision and sign are critical,
/// and where floating-point inaccuracies are unacceptable.
#[derive(Clone, Debug, PartialEq)]
pub struct SignedNumeric {
    pub value: UnsignedNumeric,
    pub is_negative: bool,
}

impl SignedNumeric {
    pub fn new(value: i128) -> Self {
        let abs_value = value.unsigned_abs();
        let is_negative = value < 0;
        Self {
            value: UnsignedNumeric::new(abs_value),
            is_negative,
        }
    }
    pub fn negate(&self) -> SignedNumeric {
        SignedNumeric {
            value: self.value.clone(),
            is_negative: !self.is_negative,
        }
    }

    pub fn checked_mul(&self, rhs: &Self) -> Option<SignedNumeric> {
        Some(SignedNumeric {
            value: self.value.checked_mul(&rhs.value)?,
            is_negative: (self.is_negative || rhs.is_negative)
                && !(self.is_negative && rhs.is_negative),
        })
    }

    pub fn checked_div(&self, rhs: &Self) -> Option<SignedNumeric> {
        Some(SignedNumeric {
            value: self.value.checked_div(&rhs.value)?,
            is_negative: (self.is_negative || rhs.is_negative)
                && !(self.is_negative && rhs.is_negative),
        })
    }

    pub fn checked_add(&self, rhs: &Self) -> Option<SignedNumeric> {
        let lhs_negative = self.is_negative;
        let rhs_negative = rhs.is_negative;

        if rhs_negative && lhs_negative {
            Some(Self {
                value: self.value.checked_add(&rhs.value)?,
                is_negative: true,
            })
        } else if rhs_negative {
            if rhs.value.greater_than(&self.value) {
                Some(Self {
                    value: rhs.value.checked_sub(&self.value)?,
                    is_negative: true,
                })
            } else {
                Some(Self {
                    value: self.value.checked_sub(&rhs.value)?,
                    is_negative: false,
                })
            }
        } else if lhs_negative {
            if self.value.greater_than(&rhs.value) {
                Some(Self {
                    value: self.value.checked_sub(&rhs.value)?,
                    is_negative: true,
                })
            } else {
                Some(Self {
                    value: rhs.value.checked_sub(&self.value)?,
                    is_negative: false,
                })
            }
        } else {
            Some(Self {
                value: self.value.checked_add(&rhs.value)?,
                is_negative: false,
            })
        }
    }

    pub fn checked_sub(&self, rhs: &Self) -> Option<SignedNumeric> {
        self.checked_add(&rhs.clone().negate())
    }

    pub fn floor(&self) -> Option<SignedNumeric> {
        Some(Self {
            value: self.value.floor()?,
            is_negative: self.is_negative,
        })
    }

    pub fn to_string(&self) -> String {
        let sign = if self.is_negative { "-" } else { "" };
        format!("{}{}", sign, self.value.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::consts::*;
    use crate::InnerUint;

    fn signed(val: u128, is_negative: bool) -> SignedNumeric {
        SignedNumeric {
            value: UnsignedNumeric::new(val),
            is_negative,
        }
    }

    #[test]
    fn test_negate() {
        let a = signed(5, false);
        let b = a.negate();
        assert_eq!(b.value, a.value);
        assert_eq!(b.is_negative, true);
        assert_eq!(b.negate(), a);
    }

    #[test]
    fn test_add_same_sign_positive() {
        let a = signed(3, false);
        let b = signed(2, false);
        let sum = a.checked_add(&b).unwrap();
        assert_eq!(sum.value.to_imprecise().unwrap(), 5);
        assert!(!sum.is_negative);
    }

    #[test]
    fn test_add_same_sign_negative() {
        let a = signed(3, true);
        let b = signed(2, true);
        let sum = a.checked_add(&b).unwrap();
        assert_eq!(sum.value.to_imprecise().unwrap(), 5);
        assert!(sum.is_negative);
    }

    #[test]
    fn test_add_opposite_sign_larger_positive() {
        let a = signed(5, false);
        let b = signed(3, true);
        let sum = a.checked_add(&b).unwrap();
        assert_eq!(sum.value.to_imprecise().unwrap(), 2);
        assert!(!sum.is_negative);
    }

    #[test]
    fn test_add_opposite_sign_larger_negative() {
        let a = signed(3, false);
        let b = signed(5, true);
        let sum = a.checked_add(&b).unwrap();
        assert_eq!(sum.value.to_imprecise().unwrap(), 2);
        assert!(sum.is_negative);
    }

    #[test]
    fn test_add_opposite_sign_equal() {
        let a = signed(4, false);
        let b = signed(4, true);
        let sum = a.checked_add(&b).unwrap();
        assert_eq!(sum.value.to_imprecise().unwrap(), 0);
        assert!(!sum.is_negative);
    }

    #[test]
    fn test_sub_positive() {
        let a = signed(10, false);
        let b = signed(3, false);
        let diff = a.checked_sub(&b).unwrap();
        assert_eq!(diff.value.to_imprecise().unwrap(), 7);
        assert!(!diff.is_negative);
    }

    #[test]
    fn test_sub_negative() {
        let a = signed(3, false);
        let b = signed(10, false);
        let diff = a.checked_sub(&b).unwrap();
        assert_eq!(diff.value.to_imprecise().unwrap(), 7);
        assert!(diff.is_negative);
    }

    #[test]
    fn test_sub_negative_minued() {
        let a = signed(3, true);
        let b = signed(10, false);
        let diff = a.checked_sub(&b).unwrap();
        assert_eq!(diff.value.to_imprecise().unwrap(), 13);
        assert!(diff.is_negative);
    }

    #[test]
    fn test_mul_signs() {
        let a = signed(3, false);
        let b = signed(2, false);
        let result = a.checked_mul(&b).unwrap();
        assert_eq!(result.value.to_imprecise().unwrap(), 6);
        assert!(!result.is_negative);

        let result = a.checked_mul(&b.negate()).unwrap();
        assert_eq!(result.value.to_imprecise().unwrap(), 6);
        assert!(result.is_negative);

        let result = a.negate().checked_mul(&b.negate()).unwrap();
        assert_eq!(result.value.to_imprecise().unwrap(), 6);
        assert!(!result.is_negative);
    }

    #[test]
    fn test_div_signs() {
        let a = signed(6, false);
        let b = signed(2, false);
        let result = a.checked_div(&b).unwrap();
        assert_eq!(result.value.to_imprecise().unwrap(), 3);
        assert!(!result.is_negative);

        let result = a.checked_div(&b.negate()).unwrap();
        assert_eq!(result.value.to_imprecise().unwrap(), 3);
        assert!(result.is_negative);

        let result = a.negate().checked_div(&b.negate()).unwrap();
        assert_eq!(result.value.to_imprecise().unwrap(), 3);
        assert!(!result.is_negative);
    }

    #[test]
    fn test_floor_behavior() {
        let base = signed(2, false);
        let mut with_decimals = base.clone();
        with_decimals.value.value = with_decimals
            .value
            .value
            .checked_add(InnerUint::from(ONE / 3))
            .unwrap();
        let floored = with_decimals.floor().unwrap();
        assert_eq!(floored.value, base.value);
        assert_eq!(floored.is_negative, false);

        let base_neg = base.negate();
        let mut neg_with_decimals = base_neg.clone();
        neg_with_decimals.value.value = neg_with_decimals
            .value
            .value
            .checked_add(InnerUint::from(ONE / 2))
            .unwrap();
        let floored = neg_with_decimals.floor().unwrap();
        assert_eq!(floored.value, base.value);
        assert_eq!(floored.is_negative, true);
    }

    #[test]
    fn test_to_string_exact() {
        let n = signed(3, false);
        assert_eq!(n.to_string(), "3.000000000000000000");
        
        let n_neg = signed(3, true);
        assert_eq!(n_neg.to_string(), "-3.000000000000000000");
    }

    #[test]
    fn test_to_string_fractional() {
        let mut n = signed(3, false);
        n.value.value += InnerUint::from(250_000_000_000_000_000u128); // +0.25
        assert_eq!(n.to_string(), "3.250000000000000000");
        
        let mut n_neg = signed(3, true);
        n_neg.value.value += InnerUint::from(250_000_000_000_000_000u128); // +0.25
        assert_eq!(n_neg.to_string(), "-3.250000000000000000");
    }
}
