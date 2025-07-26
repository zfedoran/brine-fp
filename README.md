# brine-fp

[license-image]: https://img.shields.io/badge/license-apache2-blue.svg?style=flat
![license][license-image]
[![crates.io](https://img.shields.io/crates/v/brine-fp.svg?style=flat)](https://crates.io/crates/brine-fp)

`brine-fp` is a high-precision fixed-point math library built for deterministic computation in constrained environments like the Solana SVM. It provides arithmetic, exponentiation, logarithms, and powers using configurable bit-width representations, and is optimized for low compute unit (CU) usage on-chain.

---

## ⚡ Performance

| Operation    | CU (Approx.) |
|--------------|--------------|
| `log(2)`     |     ~18,500  |
| `exp(0.5)`   |     ~15,000  |
| `pow(2, ½)`  |        ~100  |
| `frexp(2)`   |        ~150  |

These values are measured inside the Solana SVM (via test programs).

---

## Features

- Configurable bit-width fixed-point types with 18 decimal places:
  - **Default**: 192-bit unsigned & signed types
  - **With `256-bit` feature**: 256-bit unsigned & signed types
- Supports `log`, `exp`, `pow`, `floor`, `ceil`, `almost_eq`, etc.
- Remez polynomial approximations based on FreeBSD `msun`.
- Designed for deterministic and overflow-aware computation.
- Suitable for smart contract environments and financial logic.

---

## Quick Start

```rust
use brine_fp::UnsignedNumeric;

// Construct a fixed-point number: 5.0
let five = UnsignedNumeric::new(5);

// Compute its exponential
let result = five.signed().exp().unwrap();

println!("e^5 ≈ {}", result.to_string());
```

---

## Feature Flags

### 256-bit Support

Enable 256-bit precision by adding the feature flag to your `Cargo.toml`:

```toml
[dependencies]
brine-fp = { version = "0.2.0", features = ["256-bit"] }
```

This changes the internal representation from 192-bit to 256-bit, providing even larger dynamic range.

---

## Internal Representation

Each `UnsignedNumeric` wraps a `InnerUint`, representing a configurable-width unsigned integer:

**Default (192-bit)**:
```rust
InnerUint([lo, mid, hi])

// Equivalent to:
// value = lo + (mid << 64) + (hi << 128)
```

**With `256-bit` feature**:
```rust
InnerUint([lo, mid, hi, hi2])

// Equivalent to:
// value = lo + (mid << 64) + (hi << 128) + (hi2 << 192)
```

All values are scaled by `10^18`, enabling 18-digit decimal precision. 

This format ensures:

- **192-bit**: Range from `1e-18` up to `~6.3 × 10³⁹` real-world units
- **256-bit**: Range from `1e-18` up to `~1.2 × 10⁵⁸` real-world units
- High precision: 18 decimals
- Fully deterministic integer math (no `f64`, no `float`)

---

## Use Cases

- On-chain bonding curves
- DeFi math & simulations
- Deterministic pricing formulas
- Token economics
- Time-value calculations
- Anywhere you want `exp()` or `log()` without `f64`

---

### Upstream Acknowledgements

`brine-fp` is **heavily** based on prior work and stands on the shoulders of giants. The core math and algorithms are derived from:

- [Solana Labs math-spl](https://github.com/solana-labs/solana-program-library/blob/v2.0/libraries/math/src/precise_number.rs) (Apache 2)
- [Strata Foundation bonding curves](https://github.com/StrataFoundation/strata/blob/master/programs/spl-token-bonding/src/signed_precise_number.rs) (Apache 2 [with permission](https://x.com/redacted_noah/status/1948885849216876628))

---

## Contributing

Contributions are welcome! Please open issues or PRs on the GitHub repo.
