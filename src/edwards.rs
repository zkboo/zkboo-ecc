// SPDX-License-Identifier: LGPL-3.0-or-later

//! The Ed25519 twisted Edwards curve `-x² + y² = 1 + d·x²·y²` over `GF(2²⁵⁵ - 19)`, as used by
//! Solana (and Ed25519 signatures generally), implemented with 4×u64 limbs.

use crate::montgomery::select_const_coord;
use alloc::vec::Vec;
use zkboo::backend::{Backend, BooleanWordRef, WordRef};
use zkboo::word::CompositeWord;
use zkboo_modular::field::FieldRep;
use zkboo_modular::montgomery::{MontgomeryMod, MontgomeryWord, MontgomeryWordRef};

/// The Ed25519 base field modulus `p = 2²⁵⁵ - 19`, as a [MontgomeryMod].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ed25519Field;

impl MontgomeryMod<u64, 4> for Ed25519Field {
    #[inline]
    fn n(&self) -> CompositeWord<u64, 4> {
        return CompositeWord::from_be_words([
            0x7fffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffed,
        ]);
    }

    #[inline]
    fn inv_exp(&self) -> Option<CompositeWord<u64, 4>> {
        return Some(CompositeWord::from_be_words([
            0x7fffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffeb,
        ]));
    }

    #[inline]
    fn rr_mod_n(&self) -> CompositeWord<u64, 4> {
        // R = 2^256 ≡ 38 (mod p), so R² ≡ 38² = 1444.
        return CompositeWord::from_be_words([0, 0, 0, 0x5a4]);
    }

    #[inline]
    fn n_neg_inv(&self) -> CompositeWord<u64, 4> {
        return CompositeWord::from_be_words([
            0x2f286bca1af286bc,
            0xa1af286bca1af286,
            0xbca1af286bca1af2,
            0x86bca1af286bca1b,
        ]);
    }
}

/// A field element of the Ed25519 base field.
pub type Fe25519 = MontgomeryWord<u64, 4, Ed25519Field>;

/// A circuit-value field element of the Ed25519 base field.
pub type Fe25519Ref<B> = MontgomeryWordRef<B, u64, 4, Ed25519Field>;

/// The curve constant `2d`, where `d = -121665/121666`.
fn two_d() -> Fe25519 {
    return MontgomeryWord::new(
        CompositeWord::from_be_words([
            0x2406d9dc56dffce7,
            0x198e80f2eef3d130,
            0x00e0149a8283b156,
            0xebd69b9426b2f159,
        ]),
        Ed25519Field,
    );
}

/// An Ed25519 point in extended homogeneous coordinates (build-time, cleartext).
#[derive(Debug, Clone, Copy)]
pub struct EdwardsPoint {
    x: Fe25519,
    y: Fe25519,
    z: Fe25519,
    t: Fe25519,
}

/// A public Ed25519 point in Niels form `(y+x, y-x, 2d·xy)` with `z = 1`: the shape stored in
/// fixed-base comb tables and consumed by mixed addition.
#[derive(Debug, Clone, Copy)]
pub struct EdwardsNiels {
    y_plus_x: Fe25519,
    y_minus_x: Fe25519,
    t_2d: Fe25519,
}

impl EdwardsPoint {
    /// The identity point `(0, 1)`.
    pub fn identity() -> Self {
        return EdwardsPoint {
            x: Ed25519Field.zero_word(),
            y: Ed25519Field.one_word(),
            z: Ed25519Field.one_word(),
            t: Ed25519Field.zero_word(),
        };
    }

    /// The Ed25519 base point `B` (with `y = 4/5`).
    pub fn base() -> Self {
        let x = MontgomeryWord::new(
            CompositeWord::from_be_words([
                0x216936d3cd6e53fe,
                0xc0a4e231fdd6dc5c,
                0x692cc7609525a7b2,
                0xc9562d608f25d51a,
            ]),
            Ed25519Field,
        );
        let y = MontgomeryWord::new(
            CompositeWord::from_be_words([
                0x6666666666666666,
                0x6666666666666666,
                0x6666666666666666,
                0x6666666666666658,
            ]),
            Ed25519Field,
        );
        return EdwardsPoint {
            x,
            y,
            z: Ed25519Field.one_word(),
            t: x * y,
        };
    }

    /// Complete point addition (build-time).
    pub fn add(self, rhs: Self) -> Self {
        let pp = (self.y + self.x) * (rhs.y + rhs.x);
        let mm = (self.y - self.x) * (rhs.y - rhs.x);
        let tt2d = self.t * two_d() * rhs.t;
        let zz = self.z * rhs.z;
        let zz2 = zz + zz;
        let e = pp - mm;
        let h = pp + mm;
        let g = zz2 + tt2d;
        let f = zz2 - tt2d;
        return EdwardsPoint {
            x: e * f,
            y: g * h,
            z: f * g,
            t: e * h,
        };
    }

    /// Point doubling (build-time; the addition formulas are complete, so `P + P` is correct).
    pub fn double(self) -> Self {
        return self.add(self);
    }

    /// The affine coordinates `(x, y)` (build-time).
    pub fn to_affine(self) -> (Fe25519, Fe25519) {
        let z_inv = self.z.inv();
        return (self.x * z_inv, self.y * z_inv);
    }

    /// The Niels form `(y+x, y-x, 2d·xy)` of this point, normalised to `z = 1`.
    pub fn to_niels(self) -> EdwardsNiels {
        let (x, y) = self.to_affine();
        return EdwardsNiels {
            y_plus_x: y + x,
            y_minus_x: y - x,
            t_2d: x * y * two_d(),
        };
    }
}

/// An Ed25519 point in extended homogeneous coordinates (circuit values).
#[derive(Debug)]
pub struct EdwardsPointRef<B: Backend> {
    x: Fe25519Ref<B>,
    y: Fe25519Ref<B>,
    z: Fe25519Ref<B>,
    t: Fe25519Ref<B>,
}

impl<B: Backend> Clone for EdwardsPointRef<B> {
    fn clone(&self) -> Self {
        return EdwardsPointRef {
            x: self.x.clone(),
            y: self.y.clone(),
            z: self.z.clone(),
            t: self.t.clone(),
        };
    }
}

impl<B: Backend> EdwardsPointRef<B> {
    /// Mixed complete addition of a selected table point in Niels form (`z = 1`).
    fn add_niels(
        self,
        y_plus_x: Fe25519Ref<B>,
        y_minus_x: Fe25519Ref<B>,
        t_2d: Fe25519Ref<B>,
    ) -> Self {
        let pp = (self.y.clone() + self.x.clone()) * y_plus_x;
        let mm = (self.y - self.x) * y_minus_x;
        let tt2d = self.t * t_2d;
        let zz2 = self.z.clone() + self.z;
        let e = pp.clone() - mm.clone();
        let h = pp + mm;
        let g = zz2.clone() + tt2d.clone();
        let f = zz2 - tt2d;
        return EdwardsPointRef {
            x: e.clone() * f.clone(),
            y: g.clone() * h.clone(),
            z: f * g,
            t: e * h,
        };
    }

    /// The affine coordinates `(x, y)` as canonical field residues.
    pub fn to_affine(self) -> (Fe25519Ref<B>, Fe25519Ref<B>) {
        let z_inv = self.z.inv();
        return (self.x * z_inv.clone(), self.y * z_inv);
    }

    /// The 32-byte RFC 8032 point encoding: `y` in little-endian with the parity of `x` in the top
    /// bit of the final byte.
    pub fn compress(self) -> [WordRef<B, u8>; 32] {
        let (x, y) = self.to_affine();
        let sign = x.value().lsb().into();
        let y = y.value();
        let mut bytes: Vec<WordRef<B, u8>> = Vec::with_capacity(32);
        for i in 0..4 {
            bytes.extend(y.clone().word_at(i).into_le_bytes());
        }
        // Bit 7 of the top byte is clear (y < 2^255), so the XOR just sets the sign bit.
        let top = bytes.pop().expect("32 encoding bytes");
        bytes.push(top ^ (sign << 7));
        return bytes.try_into().ok().expect("32 encoding bytes");
    }
}

/// Supplies the per-window Niels-form point tables for fixed-base comb scalar multiplication: for
/// base point `P` and window width `w`, the table for window `k` holds `j · 2^{w·k} · P, j = 0 ..
/// 2^{bits_in_window(k)}`.
pub trait EdwardsWindowTables {
    /// The window width `w` in bits.
    fn window_bits(&self) -> usize;

    /// The table for window `k`.
    fn window(&mut self, k: usize) -> &[EdwardsNiels];
}

/// The default [EdwardsWindowTables]: precomputes every window's table eagerly at construction,
/// normalising all entries to Niels form with a **single batched field inversion** (Montgomery's
/// trick) — a per-entry inversion would dominate the whole multiplication on the build-time side.
#[derive(Debug, Clone)]
pub struct ComputedEdwardsWindowTables {
    window_bits: usize,
    windows: Vec<Vec<EdwardsNiels>>,
}

impl ComputedEdwardsWindowTables {
    /// A comb-table source for `base`, with the given window width.
    pub fn new(base: EdwardsPoint, window_bits: usize) -> Self {
        // All table points in extended coordinates: window k holds j · 2^{w·k} · base.
        let mut window_points: Vec<Vec<EdwardsPoint>> = Vec::new();
        let mut base_k = base;
        for k in 0..256usize.div_ceil(window_bits) {
            let bits_in_window = core::cmp::min(window_bits, 256 - k * window_bits);
            let mut row = Vec::with_capacity(1usize << bits_in_window);
            let mut acc = EdwardsPoint::identity();
            row.push(acc);
            for _ in 1..(1usize << bits_in_window) {
                acc = acc.add(base_k);
                row.push(acc);
            }
            window_points.push(row);
            for _ in 0..window_bits {
                base_k = base_k.double();
            }
        }
        // Batched inversion of every z (all nonzero on Edwards curves): prefix products,
        // one inversion, then walk back multiplying out each individual inverse.
        let flat: Vec<&EdwardsPoint> = window_points.iter().flatten().collect();
        let mut prefix = Vec::with_capacity(flat.len());
        let mut running = Ed25519Field.one_word();
        for point in &flat {
            prefix.push(running);
            running = running * point.z;
        }
        let mut running_inv = running.inv();
        let mut z_invs = alloc::vec![Ed25519Field.zero_word(); flat.len()];
        for (i, point) in flat.iter().enumerate().rev() {
            z_invs[i] = running_inv * prefix[i];
            running_inv = running_inv * point.z;
        }
        // Convert each entry to Niels form (y+x, y-x, 2d·xy) at z = 1.
        let mut z_invs = z_invs.into_iter();
        let windows = window_points
            .iter()
            .map(|row| {
                row.iter()
                    .map(|point| {
                        let z_inv = z_invs.next().expect("one inverse per entry");
                        let x = point.x * z_inv;
                        let y = point.y * z_inv;
                        return EdwardsNiels {
                            y_plus_x: y + x,
                            y_minus_x: y - x,
                            t_2d: x * y * two_d(),
                        };
                    })
                    .collect()
            })
            .collect();
        return ComputedEdwardsWindowTables {
            window_bits,
            windows,
        };
    }
}

impl EdwardsWindowTables for ComputedEdwardsWindowTables {
    #[inline]
    fn window_bits(&self) -> usize {
        return self.window_bits;
    }

    fn window(&mut self, k: usize) -> &[EdwardsNiels] {
        return &self.windows[k];
    }
}

/// Fixed-base scalar multiplication by a **secret** (circuit-value) scalar, data-oblivious.
pub fn edwards_mul_secret_scalar<B: Backend>(
    scalar: WordRef<B, u64, 4>,
    tables: &mut impl EdwardsWindowTables,
) -> EdwardsPointRef<B> {
    let w = tables.window_bits();
    let mut acc: Option<EdwardsPointRef<B>> = None;
    for k in 0..256usize.div_ceil(w) {
        let bits_in_window = core::cmp::min(w, 256 - k * w);
        let window_bits: Vec<BooleanWordRef<B>> = (0..bits_in_window)
            .map(|i| scalar.clone().bit_at(k * w + i))
            .collect();
        let table = tables.window(k);
        let y_plus_x = select_const_coord(
            &window_bits,
            &table.iter().map(|e| e.y_plus_x).collect::<Vec<_>>(),
        );
        let y_minus_x = select_const_coord(
            &window_bits,
            &table.iter().map(|e| e.y_minus_x).collect::<Vec<_>>(),
        );
        let t_2d = select_const_coord(
            &window_bits,
            &table.iter().map(|e| e.t_2d).collect::<Vec<_>>(),
        );
        acc = Some(match acc {
            None => {
                // Fold the first selection into a fresh identity accumulator built as constants.
                let identity = EdwardsPointRef {
                    x: y_plus_x.clone().into_const(CompositeWord::ZERO),
                    y: y_plus_x.clone().into_const(CompositeWord::ONE),
                    z: y_plus_x.clone().into_const(CompositeWord::ONE),
                    t: y_plus_x.clone().into_const(CompositeWord::ZERO),
                };
                identity.add_niels(y_plus_x, y_minus_x, t_2d)
            }
            Some(acc) => acc.add_niels(y_plus_x, y_minus_x, t_2d),
        });
    }
    return acc.expect("at least one window");
}
