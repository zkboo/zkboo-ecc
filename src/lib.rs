// SPDX-License-Identifier: LGPL-3.0-or-later

//! Elliptic curve cryptography primitives for the [zkboo] crate.
//!
//! Two curves are provided, both with data-oblivious fixed-base comb scalar multiplication:
//!
//! - [secp256k1] — the Bitcoin/Ethereum short-Weierstrass curve, in Jacobian coordinates over a
//!   field in Montgomery form (with a pseudo-Mersenne variant); see [weierstrass] for the generic
//!   curve, point, and window-table types.
//! - [edwards] — the Ed25519 twisted Edwards curve over `GF(2²⁵⁵ − 19)`, in extended coordinates
//!   with the complete `a = −1` addition formulas and RFC 8032 point compression.
//!
//! ⚠️ Warning: This crate has not undergone an external security review. ⚠️

#![no_std]
extern crate alloc;
pub mod edwards;
pub mod secp256k1;
pub mod weierstrass;
