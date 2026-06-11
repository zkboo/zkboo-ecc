// SPDX-License-Identifier: LGPL-3.0-or-later

//! Elliptic curve cryptography primitives for the [zkboo] crate.
//!
//! 🚧 Warning: This crate is work in progress. Implementation may be incomplete or inefficient. 🚧

#![no_std]
pub mod montgomery;
pub mod secp256k1;
