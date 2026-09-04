# Changelog

All notable changes to this crate are documented in this file, starting at 1.2.0.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and this crate adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [1.2.0] — 2026-09-04

### Changed

- Adapted to the single entry points for proving, verifying and executing.
- The `montgomery` module is now `weierstrass`.
  It holds a short-Weierstrass curve, not a Montgomery curve, and the Montgomery-form field arithmetic it is built on belongs to `zkboo-modular` under that name.
  `CurvePoint` and `CurvePointRef` become `Point` and `PointRef`; in `edwards`, `EdwardsPoint`, `EdwardsPointRef`, `EdwardsNiels`, `EdwardsWindowTables`, `ComputedEdwardsWindowTables` and `edwards_mul_secret_scalar` lose their prefix for the same reason.
