# ZKBoo-ECC

![Rust](https://img.shields.io/badge/rust-1.92+-orange.svg)
[![Crates.io](https://img.shields.io/crates/v/zkboo-ecc.svg)](https://crates.io/crates/zkboo-ecc)
[![Docs.rs](https://docs.rs/zkboo-ecc/badge.svg)](https://docs.rs/zkboo-ecc)

Elliptic curve cryptography primitives for the [ZKBoo](https://crates.io/crates/zkboo) ecosystem.

Two curves are provided, each with data-oblivious fixed-base comb scalar multiplication (public per-window tables of precomputed multiples, selected by the secret scalar bits — no in-circuit doublings):

- **secp256k1** (`montgomery`, `secp256k1`) — the Bitcoin/Ethereum short-Weierstrass curve in Jacobian coordinates, over generic Montgomery arithmetic with a faster pseudo-Mersenne field variant.
- **Ed25519** (`edwards`) — the twisted Edwards curve over GF(2²⁵⁵ − 19) in extended coordinates, with the complete `a = −1` addition formulas (no exceptional cases) and RFC 8032 point compression.

## 🚧 Warning 🚧

This crate is work in progress, not yet suitable for use in production.
Security has not been reviewed and performance has not been optimised.
Use at your own risk.

## License

[LGPLv3 © contributors.](LICENSE)
