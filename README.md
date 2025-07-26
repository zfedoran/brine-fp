# brine-fp

[license-image]: https://img.shields.io/badge/license-apache2-blue.svg?style=flat
![license][license-image]
[![crates.io](https://img.shields.io/crates/v/brine-fp.svg?style=flat)](https://crates.io/crates/brine-fp)


![image](https://github.com/user-attachments/assets/587bebdc-95e6-430a-85c6-b84ccfc36bc2)

`brine-fp` is a 192-bit fixed-point math library built for high-precision, deterministic computation in constrained environments like the Solana SVM. It provides arithmetic, exponentiation, logarithms, and powers using `u192`-based representations, and is optimized for low compute unit (CU) usage on-chain.

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

## ✨ Features

- 192-bit unsigned & signed fixed-point types with 18 decimal places.
- Supports `log`, `exp`, `pow`, `floor`, `ceil`, `almost_eq`, etc.
- Remez polynomial approximations based on FreeBSD `msun`.
- Designed for deterministic and overflow-aware computation.
- Suitable for smart contract environments and financial logic.

---

## 🚀 Quick Start

```rust
use brine_fp::UnsignedNumeric;

// Construct a fixed-point number: 5.0
let five = UnsignedNumeric::new(5);

// Compute its exponential
let result = five.signed().exp().unwrap();

println!("e^5 ≈ {}", result.to_string());
```

---

## 🧠 Internal Representation

Each `UnsignedNumeric` wraps a `InnerUint([lo, mid, hi])`, representing a 192-bit unsigned integer:

```rust
InnerUint([lo, mid, hi])

// Equivalent to:
// value = lo + (mid << 64) + (hi << 128)
```

All values are scaled by `10^18`, enabling 18-digit decimal precision. 

This format ensures:

- Extreme range: from `1e-18` up to `~6.3 × 10³⁹` real-world units
- High precision: 18 decimals
- Fully deterministic integer math (no `f64`, no `float`)

---

## 🧱 Use Cases

- On-chain bonding curves
- DeFi math & simulations
- Deterministic pricing formulas
- Token economics
- Time-value calculations
- Anywhere you want `exp()` or `log()` without `f64`

---

## 🛠 `no_std` Compatibility

This crate is designed for `no_std` environments like the Solana SVM.

If you're building in a `no_std` context, disable the default `std` feature:

```toml
[dependencies.brine-fp]
version = "0.1"
default-features = false
```

---

## Why “brine-fp”?

“Brine” evokes salt water — a precise solution. The name reflects a design focused on _precision_, _fluidity_, and _minimal bloat_ — ideal for constrained environments.

---

### Upstream Acknowledgements

`brine-fp` is **heavily** based on prior work and stands on the shoulders of giants. The core math and algorithms are derived from:

- [Solana Labs math-spl](https://github.com/solana-labs/solana-program-library/blob/v2.0/libraries/math/src/precise_number.rs) (Apache 2)
- [Strata Foundation bonding curves](https://github.com/StrataFoundation/strata/blob/master/programs/spl-token-bonding/src/signed_precise_number.rs)

---

## 🙌 Contributing

Contributions are welcome! Please open issues or PRs on the GitHub repo.
