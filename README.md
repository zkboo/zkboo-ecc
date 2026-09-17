# ZKBoo-ECC

![Rust](https://img.shields.io/badge/rust-1.92+-orange.svg)
[![Crates.io](https://img.shields.io/crates/v/zkboo-ecc.svg)](https://crates.io/crates/zkboo-ecc)
[![Docs.rs](https://docs.rs/zkboo-ecc/badge.svg)](https://docs.rs/zkboo-ecc)

Elliptic curve cryptography primitives for the [ZKBoo](https://crates.io/crates/zkboo) ecosystem.

Two curves are provided, each with data-oblivious fixed-base comb scalar multiplication (public per-window tables of precomputed multiples, selected by the secret scalar bits, with no double-and-add ladder):

- **secp256k1** (`weierstrass`, `secp256k1`) — the Bitcoin/Ethereum short-Weierstrass curve, over a field in Montgomery form with a faster pseudo-Mersenne variant.
  Points are held in Jacobian coordinates, and the comb comes in two forms: a Jacobian comb that needs nothing from the host, and an affine comb that accumulates in affine coordinates, taking each addition's slope as advice and asserting it.
  The affine comb is given the scalar's value when proving or executing and mirrors the computation on the host one window at a time to produce its slopes; it is given `None` when verifying.
  `PointRef::to_affine_advised` converts a Jacobian point to affine coordinates the same way, asserting advised coordinates instead of inverting in the circuit.
- **Ed25519** (`edwards`) — the twisted Edwards curve over GF(2²⁵⁵ − 19) in extended coordinates, with the complete `a = −1` addition formulas (no exceptional cases) and RFC 8032 point compression.

The per-window tables are public and scalar-independent, so their source is pluggable (`WindowTables`): compute them on demand with a single window's worth of memory (`ComputedWindowTables`, the default, and the natural place for a constrained prover to service a watchdog), or hold the whole table in RAM (`PrecomputedWindowTables`, for hosts, which also affords a wider window).

## ⚠️ Unaudited ⚠️

This implementation has not undergone an external security review.
Use at your own risk.

## License

[LGPLv3 © contributors.](LICENSE)
