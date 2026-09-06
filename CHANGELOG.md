# Changelog

All notable changes to this crate are documented in this file, starting at 1.2.0.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and this crate adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Changed

- The affine comb takes the scalar it multiplies by as an optional host value and mirrors it internally, one window at a time, instead of taking a precomputed table of slopes.
  The slopes were key-equivalent — each one determines which entry of a public table the window used, so the whole set determines the scalar — and the table that held them was owned by the circuit, alive for the whole proof, and unreachable by a caller wanting to erase it.
  The mirror is a private local holding the recoding residual and the running accumulator, erased when the comb returns.
  Its arithmetic now runs inside circuit execution, between two gates, where a caller's backend hook can service whatever the host needs servicing.
- The comb requests each window's table once and shares it between the oblivious select and the host mirror.
  A caller that supplies precomputed tables is therefore never routed through native point arithmetic to produce a slope, which the separate advice pass had no way to avoid.
- The circuit is unchanged gate for gate: whether the caller supplies a scalar to mirror decides where a slope's value comes from and nothing else, so a proof of a given comb is byte-identical to one made before this change.

### Added

- `PointRef::to_affine_advised` and, for Ed25519, `PointRef::to_affine_advised` and `PointRef::compress_advised`: the affine coordinates arrive as advice and the circuit asserts that they scale back to the projective ones it computed, rather than computing a modular inverse.
  Asserting a pair of coordinates costs two field multiplications; computing the inverse costs a full run of divsteps, some ninety thousand AND messages at 256 bits.
  Unlike the computed forms these reject the point at infinity, which has no affine coordinates, by making the assertion false.

### Removed

- `AffineCombAdvice`, along with its `compute`, `zeros`, `len` and `is_empty`.
  There is no advice object to construct, hold, size correctly or erase.

## [1.2.0] — 2026-09-04

### Changed

- Adapted to the single entry points for proving, verifying and executing.
- The `montgomery` module is now `weierstrass`.
  It holds a short-Weierstrass curve, not a Montgomery curve, and the Montgomery-form field arithmetic it is built on belongs to `zkboo-modular` under that name.
  `CurvePoint` and `CurvePointRef` become `Point` and `PointRef`; in `edwards`, `EdwardsPoint`, `EdwardsPointRef`, `EdwardsNiels`, `EdwardsWindowTables`, `ComputedEdwardsWindowTables` and `edwards_mul_secret_scalar` lose their prefix for the same reason.
