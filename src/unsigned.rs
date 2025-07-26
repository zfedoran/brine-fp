use super::consts::*;
use super::signed::SignedNumeric;
use super::InnerUint;
use core::convert::*;

// Based on the following implementations:
// https://github.com/solana-labs/solana-program-library/blob/v2.0/libraries/math/src/precise_number.rs
// https://github.com/StrataFoundation/strata/blob/master/programs/spl-token-bonding/src/precise_number.rs

/// A `UnsignedNumeric` is an unsigned fixed-point number with 18 decimal places of precision.
///
/// ### Internal Representation
/// Internally, the value is stored as a [`InnerUint`], which wraps a little-endian array.
/// The size depends on the feature flag:
///
/// - **Default (192-bit)**: `[u64; 3]` layout
/// - **With `256-bit` feature**: `[u64; 4]` layout
///
/// **Default layout (192-bit)**:
/// ```text
/// InnerUint([lo, mid, hi])
/// // equivalent to:
/// // value = lo + (mid << 64) + (hi << 128)
/// ```
///
/// **256-bit layout**:
/// ```text
/// InnerUint([lo, mid, hi, hi2])
/// // equivalent to:
/// // value = lo + (mid << 64) + (hi << 128) + (hi2 << 192)
/// ```
///
/// Each component contributes to the full value:
///
/// **Default**: `value = (hi × 2^128) + (mid × 2^64) + lo`
/// **256-bit**: `value = (hi2 × 2^192) + (hi × 2^128) + (mid × 2^64) + lo`
///
/// ### Fixed-Point Scaling
/// All values are scaled by [`ONE`] (10^18). That is, the internal number is interpreted
/// as `raw / ONE` to recover its real-world value.
///
/// Examples:
/// - `InnerUint([1_000_000_000_000_000_000, 0, 0])` → 1.0
/// - `InnerUint([500_000_000_000_000_000, 0, 0])` → 0.5
/// - `InnerUint([2_000_000_000_000_000_000, 0, 0])` → 2.0
///
/// ### Example: High-Bit Usage
///
/// **Default (192-bit)**:
/// When you write:
/// ```text
/// let a = UnsignedNumeric::from_values(0, 0, 1);
/// ```
/// This initializes the internal 192-bit value with the array `[0, 0, 1]`.
/// In this representation:
///
/// - `0` is the least significant 64 bits (`lo`)
/// - `0` is the middle 64 bits (`mid`)
/// - `1` is the most significant 64 bits (`hi`)
///
/// The actual 192-bit value is computed as:
///
/// ```text
/// value = (1 × 2^128) + (0 × 2^64) + 0 = 2^128
///       = 340282366920938463463374607431768211456
/// ```
///
/// **256-bit feature**:
/// When you write:
/// ```text
/// let a = UnsignedNumeric::from_values(0, 0, 0, 1);
/// ```
/// This initializes the internal 256-bit value with the array `[0, 0, 0, 1]`.
/// In this representation:
///
/// - `0` is the least significant 64 bits (`lo`)
/// - `0` is the middle 64 bits (`mid`)
/// - `0` is the high 64 bits (`hi`)
/// - `1` is the most significant 64 bits (`hi2`)
///
/// The actual 256-bit value is computed as:
///
/// ```text
/// value = (1 × 2^192) + (0 × 2^128) + (0 × 2^64) + 0 = 2^192
///       = 6277101735386680763835789423207666416102355444464034512896
/// ```
///
/// Since this is a fixed-point number, the real-world value is:
///
/// **Default**: `real_value = value / 10^18 = 340282366920938463463.374607431768211456`
/// **256-bit**: `real_value = value / 10^18 = 6277101735386680763835789423207666416102355444464034512896 / 10^18`
///
/// This system allows for both extremely high precision and a vast dynamic range,
/// making [`UnsignedNumeric`] ideal for financial, scientific, or blockchain applications
/// where `f64` or even `u128` would lose accuracy or overflow.
#[derive(Clone, Debug, PartialEq)]
pub struct UnsignedNumeric {
    /// Internal value stored as a 192-bit integer, scaled by ONE (10^18).
    pub value: InnerUint,
}

impl UnsignedNumeric {
    /// Returns a `UnsignedNumeric` representing 0.0.
    pub fn zero() -> Self {
        Self { value: zero() }
    }

    /// Returns a `UnsignedNumeric` representing 1.0.
    pub fn one() -> Self {
        Self { value: one() }
    }

    /// Constructs a `UnsignedNumeric` from an integer value by scaling it by ONE (10^18).
    /// For example, `new(7)` produces `7.0`.
    pub fn new(value: u128) -> Self {
        // `one()` is 10^18 and 10^18 * u128::MAX will always fit within 196 bits
        let value = InnerUint::from(value).checked_mul(one()).unwrap();
        Self { value }
    }

    /// Constructs a `UnsignedNumeric` from a `u128` that is already scaled by ONE (i.e. in fixed-point space).
    /// This bypasses internal multiplication and is useful for constants or pre-scaled data.
    pub fn from_scaled_u128(value: u128) -> Self {
        Self {
            value: InnerUint::from(value),
        }
    }

    /// Constructs a `UnsignedNumeric` directly from a raw `[u64; 3]` value.
    /// The input is interpreted as already scaled (fixed-point).
    /// Layout is little-endian: `[lo, mid, hi]` = `lo + (mid << 64) + (hi << 128)`.
    #[cfg(not(feature = "256-bit"))]
    pub fn from_values(lo: u64, mid: u64, hi: u64) -> Self {
        Self {
            value: InnerUint([lo, mid, hi]),
        }
    }

    /// Constructs a `UnsignedNumeric` directly from a raw `[u64; 4]` value.
    /// The input is interpreted as already scaled (fixed-point).
    /// Layout is little-endian: `[lo, mid, hi, hi2]` = `lo + (mid << 64) + (hi << 128) + (hi2 << 192)`.
    #[cfg(feature = "256-bit")]
    pub fn from_values(lo: u64, mid: u64, hi: u64, hi2: u64) -> Self {
        Self {
            value: InnerUint([lo, mid, hi, hi2]),
        }
    }

    /// Converts this `UnsignedNumeric` into a raw `[u8; 24]` representation.
    #[cfg(not(feature = "256-bit"))]
    pub fn to_bytes(&self) -> [u8; 24] {
        let InnerUint([lo, mid, hi]) = self.value;

        let mut bytes = [0u8; 24];
        bytes[0..8].copy_from_slice(&lo.to_le_bytes());
        bytes[8..16].copy_from_slice(&mid.to_le_bytes());
        bytes[16..24].copy_from_slice(&hi.to_le_bytes());

        bytes
    }

    /// Converts this `UnsignedNumeric` into a raw `[u8; 32]` representation.
    #[cfg(feature = "256-bit")]
    pub fn to_bytes(&self) -> [u8; 32] {
        let InnerUint([lo, mid, hi, hi2]) = self.value;

        let mut bytes = [0u8; 32];
        bytes[0..8].copy_from_slice(&lo.to_le_bytes());
        bytes[8..16].copy_from_slice(&mid.to_le_bytes());
        bytes[16..24].copy_from_slice(&hi.to_le_bytes());
        bytes[24..32].copy_from_slice(&hi2.to_le_bytes());

        bytes
    }

    /// Converts a raw `[u8; 24]` representation into a `UnsignedNumeric`.
    #[cfg(not(feature = "256-bit"))]
    pub fn from_bytes(bytes: &[u8; 24]) -> Self {
        let lo = u64::from_le_bytes(bytes[0..8].try_into().unwrap());
        let mid = u64::from_le_bytes(bytes[8..16].try_into().unwrap());
        let hi = u64::from_le_bytes(bytes[16..24].try_into().unwrap());

        Self {
            value: InnerUint([lo, mid, hi]),
        }
    }

    /// Converts a raw `[u8; 32]` representation into a `UnsignedNumeric`.
    #[cfg(feature = "256-bit")]
    pub fn from_bytes(bytes: &[u8; 32]) -> Self {
        let lo = u64::from_le_bytes(bytes[0..8].try_into().unwrap());
        let mid = u64::from_le_bytes(bytes[8..16].try_into().unwrap());
        let hi = u64::from_le_bytes(bytes[16..24].try_into().unwrap());
        let hi2 = u64::from_le_bytes(bytes[24..32].try_into().unwrap());

        Self {
            value: InnerUint([lo, mid, hi, hi2]),
        }
    }

    /// Converts this `UnsignedNumeric` into a regular `u128` by dividing by ONE.
    /// Applies rounding correction to avoid always flooring the result.
    /// Returns `None` if the division would overflow or the result exceeds `u128::MAX`.
    pub fn to_imprecise(&self) -> Option<u128> {
        self.value
            .checked_add(Self::rounding_correction())?
            .checked_div(one())
            .map(|v| v.as_u128())
    }

    /// Converts this `UnsignedNumeric` into a signed version,
    /// wrapping it in a `SignedNumeric` with `is_negative = false`.
    /// Useful when beginning arithmetic that may result in negative values.
    pub fn signed(&self) -> SignedNumeric {
        SignedNumeric {
            value: self.clone(),
            is_negative: false,
        }
    }

    /// Returns a rounding correction (0.5) used in division/multiplication
    /// to mitigate truncation from integer floor behavior.
    /// This simulates "round-to-nearest" by adding half the divisor.
    fn rounding_correction() -> InnerUint {
        InnerUint::from(ONE / 2)
    }

    /// Compares two `UnsignedNumeric`s for approximate equality,
    /// allowing for a configurable `precision` window.
    pub fn almost_eq(&self, rhs: &Self, precision: InnerUint) -> bool {
        let (difference, _) = self.unsigned_sub(rhs);
        difference.value < precision
    }

    /// Returns `true` if `self < rhs` in fixed-point terms.
    pub fn less_than(&self, rhs: &Self) -> bool {
        self.value < rhs.value
    }

    /// Returns `true` if `self > rhs`.
    pub fn greater_than(&self, rhs: &Self) -> bool {
        self.value > rhs.value
    }

    /// Returns `true` if `self <= rhs`.
    pub fn less_than_or_equal(&self, rhs: &Self) -> bool {
        self.value <= rhs.value
    }

    /// Returns `true` if `self >= rhs`.
    pub fn greater_than_or_equal(&self, rhs: &Self) -> bool {
        self.value >= rhs.value
    }

    /// Rounds down to the nearest whole number by truncating fractional digits.
    pub fn floor(&self) -> Option<Self> {
        let value = self.value.checked_div(one())?.checked_mul(one())?;
        Some(Self { value })
    }

    /// Rounds up to the nearest whole number.
    pub fn ceiling(&self) -> Option<Self> {
        let value = self
            .value
            .checked_add(one().checked_sub(InnerUint::from(1))?)?
            .checked_div(one())?
            .checked_mul(one())?;
        Some(Self { value })
    }

    /// Divides `self / rhs` in fixed-point space, maintaining precision.
    /// Applies rounding correction to minimize truncation error.
    /// Returns `None` on divide-by-zero or overflow.
    pub fn checked_div(&self, rhs: &Self) -> Option<Self> {
        if *rhs == Self::zero() {
            return None;
        }
        match self.value.checked_mul(one()) {
            Some(v) => {
                let value = v
                    .checked_add(Self::rounding_correction())?
                    .checked_div(rhs.value)?;
                Some(Self { value })
            }
            None => {
                let value = self
                    .value
                    .checked_add(Self::rounding_correction())?
                    .checked_div(rhs.value)?
                    .checked_mul(one())?;
                Some(Self { value })
            }
        }
    }

    /// Multiplies two `UnsignedNumeric`s and returns the result in fixed-point space.
    /// Automatically divides by ONE to maintain correct scaling, and applies rounding correction.
    /// Falls back to a reduced-precision path if full multiplication would overflow.
    pub fn checked_mul(&self, rhs: &Self) -> Option<Self> {
        match self.value.checked_mul(rhs.value) {
            Some(v) => {
                let value = v
                    .checked_add(Self::rounding_correction())?
                    .checked_div(one())?;
                Some(Self { value })
            }
            None => {
                let value = if self.value >= rhs.value {
                    self.value.checked_div(one())?.checked_mul(rhs.value)?
                } else {
                    rhs.value.checked_div(one())?.checked_mul(self.value)?
                };
                Some(Self { value })
            }
        }
    }

    /// Adds two precise numbers. Returns `None` on overflow.
    pub fn checked_add(&self, rhs: &Self) -> Option<Self> {
        let value = self.value.checked_add(rhs.value)?;
        Some(Self { value })
    }

    /// Subtracts `rhs` from `self`. Returns `None` if the result would be negative.
    pub fn checked_sub(&self, rhs: &Self) -> Option<Self> {
        let value = self.value.checked_sub(rhs.value)?;
        Some(Self { value })
    }

    /// Computes the absolute difference between two numbers.
    /// Returns the result and a boolean indicating whether the result was originally negative.
    pub fn unsigned_sub(&self, rhs: &Self) -> (Self, bool) {
        match self.value.checked_sub(rhs.value) {
            None => {
                let value = rhs.value.checked_sub(self.value).unwrap();
                (Self { value }, true)
            }
            Some(value) => (Self { value }, false),
        }
    }

    /// Converts the precise number into a human-readable decimal string with full 18-digit precision.
    ///
    /// For example, a number representing 3.1415 will be displayed as:
    /// `"3.141500000000000000"`
    pub fn to_string(&self) -> String {
        let whole = self.floor().unwrap().to_imprecise().unwrap();
        let decimals = self
            .checked_sub(&UnsignedNumeric::new(whole))
            .unwrap()
            .checked_mul(&UnsignedNumeric::new(ONE))
            .unwrap()
            .to_imprecise()
            .unwrap();
        format!("{}.{:0>width$}", whole, decimals, width = 18)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn max_numeric() -> UnsignedNumeric {
        UnsignedNumeric {
            value: InnerUint::MAX,
        }
    }

    #[test]
    fn test_zero_and_one() {
        assert_eq!(UnsignedNumeric::zero().value, InnerUint::from(0));
        assert_eq!(UnsignedNumeric::one().value, InnerUint::from(ONE));
    }

    #[test]
    fn test_from_scaled_u128() {
        let n = UnsignedNumeric::from_scaled_u128(42 * ONE);
        assert_eq!(n.to_imprecise().unwrap(), 42);
    }

    #[test]
    fn test_to_string_exact() {
        let n = UnsignedNumeric::new(3);
        assert_eq!(n.to_string(), "3.000000000000000000");
    }

    #[test]
    fn test_to_string_fractional() {
        let mut n = UnsignedNumeric::new(3);
        n.value += InnerUint::from(250_000_000_000_000_000u128); // +0.25
        assert_eq!(n.to_string(), "3.250000000000000000");
    }

    #[test]
    fn test_checked_add() {
        let a = UnsignedNumeric::new(1);
        let b = UnsignedNumeric::new(2);
        let sum = a.checked_add(&b).unwrap();
        assert_eq!(sum.to_imprecise().unwrap(), 3);
    }

    #[test]
    fn test_checked_sub_underflow() {
        let a = UnsignedNumeric::new(1);
        let b = UnsignedNumeric::new(2);
        assert!(a.checked_sub(&b).is_none());
    }

    #[test]
    fn test_checked_sub_valid() {
        let a = UnsignedNumeric::new(3);
        let b = UnsignedNumeric::new(1);
        let result = a.checked_sub(&b).unwrap();
        assert_eq!(result.to_imprecise().unwrap(), 2);
    }

    #[test]
    fn test_checked_mul_simple() {
        let a = UnsignedNumeric::new(2);
        let b = UnsignedNumeric::new(3);
        let product = a.checked_mul(&b).unwrap();
        assert_eq!(product.to_imprecise().unwrap(), 6);
    }

    #[test]
    fn test_checked_div_exact() {
        let a = UnsignedNumeric::new(6);
        let b = UnsignedNumeric::new(2);
        let result = a.checked_div(&b).unwrap();
        assert_eq!(result.to_imprecise().unwrap(), 3);
    }

    #[test]
    fn test_checked_div_rounded() {
        let a = UnsignedNumeric::new(1);
        let b = UnsignedNumeric::new(3); // 1 / 3

        let result = a.checked_div(&b).unwrap();
        let expected = UnsignedNumeric::from_scaled_u128(333_333_333_333_333_333); // ~0.333...

        assert!(result.almost_eq(&expected, InnerUint::from(1_000_000)));
    }

    #[test]
    fn test_unsigned_sub_positive() {
        let a = UnsignedNumeric::new(7);
        let b = UnsignedNumeric::new(3);
        let (result, is_negative) = a.unsigned_sub(&b);
        assert_eq!(result.to_imprecise().unwrap(), 4);
        assert!(!is_negative);
    }

    #[test]
    fn test_unsigned_sub_negative() {
        let a = UnsignedNumeric::new(3);
        let b = UnsignedNumeric::new(7);
        let (result, is_negative) = a.unsigned_sub(&b);
        assert_eq!(result.to_imprecise().unwrap(), 4);
        assert!(is_negative);
    }

    #[test]
    fn test_almost_eq_within_precision() {
        let a = UnsignedNumeric::new(5);
        let mut b = a.clone();
        b.value += InnerUint::from(10); // Very slight difference

        assert!(a.almost_eq(&b, InnerUint::from(20)));
        assert!(!a.almost_eq(&b, InnerUint::from(5)));
    }

    #[test]
    fn test_comparisons() {
        let a = UnsignedNumeric::new(1);
        let b = UnsignedNumeric::new(2);
        assert!(a.less_than(&b));
        assert!(b.greater_than(&a));
        assert!(a.less_than_or_equal(&b));
        assert!(b.greater_than_or_equal(&a));
        assert!(a.less_than_or_equal(&a));
        assert!(a.greater_than_or_equal(&a));
    }

    #[test]
    fn test_signed_conversion() {
        let u = UnsignedNumeric::new(42);
        let s = u.signed();
        assert_eq!(s.value, u);
        assert!(!s.is_negative);
    }

    #[test]
    fn test_serialization() {
        #[cfg(not(feature = "256-bit"))]
        {
            let original = UnsignedNumeric::from_values(123, 456, 789);
            let bytes = original.to_bytes();
            let recovered = UnsignedNumeric::from_bytes(&bytes);

            assert_eq!(original, recovered);
        }
        #[cfg(feature = "256-bit")]
        {
            let original = UnsignedNumeric::from_values(123, 456, 789, 101112);
            let bytes = original.to_bytes();
            let recovered = UnsignedNumeric::from_bytes(&bytes);

            assert_eq!(original, recovered);
        }
    }

    #[test]
    fn test_floor() {
        let whole_number = UnsignedNumeric::new(2);
        let mut decimal_number = UnsignedNumeric::new(2);
        decimal_number.value += InnerUint::from(1);
        let floor = decimal_number.floor().unwrap();
        let floor_again = floor.floor().unwrap();
        assert_eq!(whole_number.value, floor.value);
        assert_eq!(whole_number.value, floor_again.value);
    }

    #[test]
    fn test_ceiling() {
        let whole_number = UnsignedNumeric::new(2);
        let mut decimal_number = UnsignedNumeric::new(2);
        decimal_number.value -= InnerUint::from(1);
        let ceiling = decimal_number.ceiling().unwrap();
        let ceiling_again = ceiling.ceiling().unwrap();
        assert_eq!(whole_number.value, ceiling.value);
        assert_eq!(whole_number.value, ceiling_again.value);
    }

    #[test]
    fn test_add_overflow() {
        let a = max_numeric();
        let b = UnsignedNumeric::one();
        assert!(a.checked_add(&b).is_none(), "Expected overflow on add");
    }

    #[test]
    fn test_mul_overflow() {
        let a = max_numeric();
        let b = UnsignedNumeric::new(2); // 2.0 in scaled form

        let result = a.checked_mul(&b);
        assert!(result.is_none(), "Expected overflow on multiply");
    }

    #[test]
    fn test_mul_fallback_path() {
        let a = UnsignedNumeric::new(1_000_000_000_000u128); // large-ish value
        let b = UnsignedNumeric::new(2);

        let result = a.checked_mul(&b).unwrap();
        assert_eq!(result.to_imprecise().unwrap(), 2_000_000_000_000);
    }

    #[test]
    fn test_mul_large_by_large_overflow() {
        #[cfg(not(feature = "256-bit"))]
        {
            let a = UnsignedNumeric {
                value: InnerUint([0, 0, 1]), // 2^128
            };
            let b = a.clone(); // 2^128 * 2^128 = 2^256, definitely too large

            let result = a.checked_mul(&b);
            assert!(result.is_none(), "Expected overflow on large * large");
        }
        #[cfg(feature = "256-bit")]
        {
            let a = UnsignedNumeric {
                value: InnerUint([0, 0, 0, 1]), // 2^192
            };
            let b = a.clone(); // 2^192 * 2^192 = 2^384, definitely too large

            let result = a.checked_mul(&b);
            assert!(result.is_none(), "Expected overflow on large * large");
        }
    }

    #[test]
    fn test_div_by_zero() {
        let a = UnsignedNumeric::new(42);
        let zero = UnsignedNumeric::zero();

        assert!(a.checked_div(&zero).is_none(), "Expected div by zero to fail");
    }

    #[test]
    fn test_floor_overflow_fallback() {
        // floor() performs: value / ONE * ONE
        // If value is MAX, this can overflow
        let a = max_numeric();
        let result = a.floor();
        assert!(result.is_some(), "Should handle overflow in floor safely");
    }

    #[test]
    fn test_ceiling_overflow() {
        // ceiling() performs: (value + ONE - 1) / ONE * ONE
        // Adding ONE - 1 to MAX will overflow
        let a = max_numeric();
        let result = a.ceiling();
        assert!(result.is_none(), "Expected overflow in ceiling()");
    }

    #[test]
    fn test_rounding_correction_addition_overflow() {
        let a = max_numeric();
        // This simulates rounding correction inside `checked_div`
        let corrected = a.value.checked_add(UnsignedNumeric::rounding_correction());
        assert!(corrected.is_none(), "Expected overflow in rounding correction");
    }
}
