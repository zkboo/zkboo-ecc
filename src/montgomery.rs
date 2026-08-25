// SPDX-License-Identifier: LGPL-3.0-or-later

//! Elliptic curve cryptography primitives for the [zkboo] crate, based on Montgomery arithmetic.

use alloc::vec::Vec;
use core::{
    fmt::Debug,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};
use zkboo::{
    backend::{Backend, BooleanWordRef, Frontend, WordRef},
    word::{CompositeWord, Word, WordLike},
};
use zkboo_modular::field::FieldRep;
use zkboo_modular::montgomery::{
    MontgomeryBooleanWordRefSelector, MontgomeryFrontendIO, MontgomeryMod, MontgomeryWord,
    MontgomeryWordRef,
};

/// An elliptic curve in short Weierstrass form, defined by the equation `y^2 = x^3 + ax + b`
/// over a prime field, with coefficients in Montgomery form.
pub trait Curve<W: Word, const N: usize>: Clone + Copy + PartialEq + Eq + Debug {
    type P: FieldRep<W, N>;

    /// The modulus of the underlying prime field, with modular operations in Montgomery form.
    fn p(&self) -> Self::P;

    /// The curve parameter `a`, in Montgomery form.
    fn a(&self) -> MontgomeryWord<W, N, Self::P>;

    /// The curve parameter `b`, in Montgomery form.
    fn b(&self) -> MontgomeryWord<W, N, Self::P>;

    /// The base point `g` of the curve.
    ///
    /// Implementations must guarantee that `self.g().curve() == self`.
    fn g(&self) -> CurvePoint<W, N, Self>;

    /// The order of the base point [`g`](Curve::g).
    ///
    /// Implementations must guarantee that this is the least non-negative integer `n` such that
    /// `self.g() * self.n() == self.p().one_word()`.
    fn n(&self) -> CompositeWord<W, N>;

    /// The zero element of the curve.
    fn zero(&self) -> CurvePoint<W, N, Self> {
        return CurvePoint::_inf(*self);
    }

    /// A point on the curve in Jacobian representation.
    fn point(
        &self,
        x: MontgomeryWord<W, N, Self::P>,
        y: MontgomeryWord<W, N, Self::P>,
        z: MontgomeryWord<W, N, Self::P>,
    ) -> CurvePoint<W, N, Self> {
        assert!(self.contains_const([x, y, z]), "Point not on curve");
        return self.unchecked_point(x, y, z);
    }

    /// A point on the curve in affine representation.
    fn point_affine(
        &self,
        x: MontgomeryWord<W, N, Self::P>,
        y: MontgomeryWord<W, N, Self::P>,
    ) -> CurvePoint<W, N, Self> {
        assert!(
            self.contains_const([x, y, self.p().one_word()]),
            "Point not on curve"
        );
        return self.unchecked_point_affine(x, y);
    }

    /// An unchecked point on the curve in Jacobian representation.
    ///
    /// ⚠️ Safety: The caller must ensure that the point is on the curve.
    /// Failure to do so may result in incorrect behaviour.
    fn unchecked_point(
        &self,
        x: MontgomeryWord<W, N, Self::P>,
        y: MontgomeryWord<W, N, Self::P>,
        z: MontgomeryWord<W, N, Self::P>,
    ) -> CurvePoint<W, N, Self> {
        return CurvePoint::_jacobian(x, y, z, *self);
    }

    /// An unchecked point on the curve in affine representation.
    ///
    /// ⚠️ Safety: The caller must ensure that the point is on the curve.
    /// Failure to do so may result in incorrect behaviour.
    fn unchecked_point_affine(
        &self,
        x: MontgomeryWord<W, N, Self::P>,
        y: MontgomeryWord<W, N, Self::P>,
    ) -> CurvePoint<W, N, Self> {
        return CurvePoint::_affine(x, y, *self);
    }

    /// Helper method to check if a point with given coordinates is on the curve.
    fn contains_const(&self, coords: [MontgomeryWord<W, N, Self::P>; 3]) -> bool {
        let (p, a, b) = (self.p(), self.a(), self.b());
        let [x, y, z] = coords;
        assert_eq!(p, x.modulus(), "Incorrect modulus for x coordinate.");
        assert_eq!(p, y.modulus(), "Incorrect modulus for y coordinate.");
        assert_eq!(p, z.modulus(), "Incorrect modulus for z coordinate.");
        if z.is_zero() {
            return true;
        }
        let z2 = z * z;
        let z4 = z2 * z2;
        let z6 = z4 * z2;
        return y * y == x * x * x + a * x * z4 + b * z6;
    }

    /// Fixed-base scalar multiplication by a **secret** (circuit-value) scalar, data-oblivious.
    fn mul_secret_scalar<B: Backend>(
        &self,
        scalar: WordRef<B, W, N>,
        tables: &mut impl WindowTables<W, N, Self>,
    ) -> CurvePointRef<B, W, N, Self> {
        let width = W::WIDTH * N;
        let w = tables.window_bits();
        // A one-bit window leaves the magnitude mux with no index bits and a single-entry table,
        // which `select_const_coord` cannot express (it has no backend handle to allocate the lone
        // constant from). Reject it here rather than panicking deeper in the mux.
        assert!(w >= 2, "window width must be at least 2 bits, got {w}");
        let num_windows = comb_window_count(width, w);
        // Parity fix: work with an odd representative t ≡ d (mod n). Adding the group order n (odd)
        // to an even scalar makes it odd without changing d·base (n·base = O); an odd scalar is left
        // as is. So t is odd and t < 2^width + n < 2^(width+1): its (width+1)-th bit is `carry`,
        // handled once below.
        let d_even = !scalar.clone().lsb();
        let addend = d_even.select_const_const(self.n(), CompositeWord::<W, N>::ZERO);
        let (mut t, carry) = scalar.overflowing_add(addend);
        let mut res: Option<CurvePointRef<B, W, N, Self>> = None;
        for k in 0..num_windows {
            let is_top = k + 1 == num_windows;
            let (sign_neg, index_bits): (BooleanWordRef<B>, Vec<BooleanWordRef<B>>) = if is_top {
                // Top window: the regular recoding's final digit is the remaining value t itself,
                // which is odd, positive, and small (< 2^w). Its sign is +, its magnitude is t, so
                // idx = (t − 1) / 2 = bits 1.. of t, with no sign masking.
                let sign_neg = t.clone().into_const_bool(false);
                let bits = (0..w - 1).map(|j| t.clone().bit_at(1 + j)).collect();
                (sign_neg, bits)
            } else {
                // Regular (Joye–Tunstall) recoding: the signed digit is e_k = (t mod 2^(w+1)) − 2^w,
                // odd and in [−(2^w−1), 2^w−1]. Its sign is the (w)-th bit's complement; its
                // magnitude 2·idx+1 gives idx = (bits 1.. of t) XOR-masked by the sign.
                let sign_neg = !t.clone().bit_at(w);
                let bits = (0..w - 1)
                    .map(|j| t.clone().bit_at(1 + j) ^ sign_neg.clone())
                    .collect();
                (sign_neg, bits)
            };
            let selected = select_signed_point(&index_bits, sign_neg, tables.window(k), *self);
            res = Some(match res {
                None => selected,
                // Mixed add for every window but the last; complete add for the last window, the
                // only one where the accumulated partial sum can equal or oppose the table point.
                Some(r) if !is_top => r.madd(selected),
                Some(r) => r + selected,
            });
            // Advance the recoding for the next (non-top) window: t ← (t − e_k) >> w =
            // ((t >> (w+1)) << 1) | 1. On the first step only, fold the (width+1)-th bit (`carry`)
            // into its new position, bit (width − w); thereafter the true t fits the word.
            if !is_top {
                let mut t_next = ((t >> (w + 1)) << 1).bitor_const(CompositeWord::<W, N>::ONE);
                if k == 0 {
                    t_next = t_next ^ (WordRef::from_bool(carry.clone()) << (width - w));
                }
                t = t_next;
            }
        }
        // `width >= 1`, so there is at least one window and `res` is always set.
        return res.expect("at least one window");
    }
}

/// A point on an elliptic curve in short Weierstrass form, in Jacobian representation,
/// with coordinates in Montgomery form.
#[derive(Debug, Clone, Copy, Hash)]
pub struct CurvePoint<W: Word, const N: usize, C: Curve<W, N>> {
    x: MontgomeryWord<W, N, C::P>,
    y: MontgomeryWord<W, N, C::P>,
    z: MontgomeryWord<W, N, C::P>,
    curve: C,
}

impl<W: Word, const N: usize, C: Curve<W, N>> CurvePoint<W, N, C> {
    /// Helper constructor for points in affine representation.
    fn _affine(x: MontgomeryWord<W, N, C::P>, y: MontgomeryWord<W, N, C::P>, curve: C) -> Self {
        return Self {
            x,
            y,
            z: curve.p().one_word(),
            curve,
        };
    }

    /// Helper constructor for points in Jacobian representation.
    fn _jacobian(
        x: MontgomeryWord<W, N, C::P>,
        y: MontgomeryWord<W, N, C::P>,
        z: MontgomeryWord<W, N, C::P>,
        curve: C,
    ) -> Self {
        return Self { x, y, z, curve };
    }

    /// Helper constructor for the infinite point on a curve.
    fn _inf(curve: C) -> Self {
        let zero = curve.p().zero_word();
        let one = curve.p().one_word();
        return Self {
            x: zero,
            y: one,
            z: zero,
            curve,
        };
    }

    /// Helper constructor to conditionally construct either the infinite point or
    /// a Jacobian point, based on a boolean flag.
    fn _inf_or_jacobian(
        is_inf: bool,
        x: MontgomeryWord<W, N, C::P>,
        y: MontgomeryWord<W, N, C::P>,
        z: MontgomeryWord<W, N, C::P>,
        curve: C,
    ) -> Self {
        return if is_inf {
            curve.zero()
        } else {
            Self::_jacobian(x, y, z, curve)
        };
    }

    /// Get the coordinates of the point as an array.
    pub fn coords(&self) -> [MontgomeryWord<W, N, C::P>; 3] {
        return [self.x, self.y, self.z];
    }

    /// Convert the point to affine representation.
    ///
    /// Available only for Montgomery fields, as it uses the build-time constant inverse
    /// [`MontgomeryWord::inv`]. The in-circuit [`CurvePointRef::to_affine`] works for any field.
    pub fn to_affine(self) -> Self
    where
        C::P: MontgomeryMod<W, N>,
    {
        if self.is_inf() {
            return self;
        }
        let z_inv = self.z.inv();
        let z_inv_sq = z_inv * z_inv;
        let x_affine = self.x * z_inv_sq;
        let y_affine = self.y * z_inv_sq * z_inv;
        return Self::_affine(x_affine, y_affine, self.curve);
    }

    /// Check if the point is in affine representation, i.e. if `z == 1`.
    pub fn is_affine(&self) -> bool {
        return self.z == self.curve.p().one_word();
    }

    /// Check if the point is the infinite point, i.e. if `z == 0`.
    pub fn is_inf(&self) -> bool {
        return self.z.is_zero();
    }

    /// Get the curve that the point is on.
    pub fn curve(&self) -> C {
        return self.curve;
    }

    /// Destructure the point into its coordinates and curve.
    pub fn destructure(
        self,
    ) -> (
        MontgomeryWord<W, N, C::P>,
        MontgomeryWord<W, N, C::P>,
        MontgomeryWord<W, N, C::P>,
        C,
    ) {
        return (self.x, self.y, self.z, self.curve);
    }

    /// Point doubling on the [Curve].
    pub fn double(self) -> Self {
        let (x, y, z, curve) = self.destructure();
        if z.is_zero() | y.is_zero() {
            return curve.zero();
        }
        let yy = y * y;
        let xyy = x * yy;
        let xx = x * x;
        let xyy2 = xyy + xyy;
        let s = xyy2 + xyy2;
        let m = xx + xx + xx;
        let s2 = s + s;
        let res_x = m * m - s2;
        let yyyy = yy * yy;
        let yyyy2 = yyyy + yyyy;
        let yyyy4 = yyyy2 + yyyy2;
        let yyyy8 = yyyy4 + yyyy4;
        let res_y = m * (s - res_x) - yyyy8;
        let yz = y * z;
        let res_z = yz + yz;
        return Self {
            x: res_x,
            y: res_y,
            z: res_z,
            curve,
        };
    }

    /// Check if two points are equal.
    pub fn eq(self, rhs: Self) -> bool {
        let (x1, y1, z1, curve1) = self.destructure();
        let (x2, y2, z2, curve2) = rhs.destructure();
        assert_eq!(curve1, curve2, "Cannot compare points on different curves.");
        if z1.is_zero() && z2.is_zero() {
            return true;
        }
        if z1.is_zero() || z2.is_zero() {
            return false;
        }
        let z1z1 = z1 * z1;
        let z2z2 = z2 * z2;
        if x1 * z2z2 != x2 * z1z1 {
            return false;
        }
        if y1 * z2z2 * z2 != y2 * z1z1 * z1 {
            return false;
        }
        return true;
    }

    pub fn ne(self, rhs: Self) -> bool {
        return !self.eq(rhs);
    }

    /// Fixed-base scalar multiplication of this base point by a **secret** (circuit-value)
    /// scalar, data-oblivious, computing the window tables on demand at the default window
    /// width ([`DEFAULT_COMB_WINDOW_BITS`]).
    ///
    /// This is the convenience form of [`Curve::mul_secret_scalar`]: it builds a
    /// [`ComputedWindowTables`] for this base point and multiplies. For control over the
    /// window width, or to supply a different table source — flash-resident tables, or
    /// on-demand computation that services a platform watchdog while the native table
    /// arithmetic runs — build a [`WindowTables`] yourself and call
    /// [`Curve::mul_secret_scalar`] directly.
    ///
    /// A host prover should do exactly that, with a [`PrecomputedWindowTables`] at
    /// [`HOST_COMB_WINDOW_BITS`]: this form rebuilds every window's table on every circuit pass,
    /// and the wider window is a further 1.7× off the gate count.
    ///
    /// For secp256k1 this is an order of magnitude cheaper than [`CurvePointRef::mul`] by a secret
    /// scalar. The window width trades nonlinear gates against the per-window table size
    /// (`2^(w−1)` odd multiples); measured for a full secp256k1 `d·G` with affine output over the
    /// pseudo-Mersenne field (vs. 18,028,168 nonlinear and_msgs for the ladder):
    ///
    /// | w | nl and_msgs | speedup | peak table |
    /// |---|------------:|--------:|-----------:|
    /// | 4 |   1,770,659 |  10.2×  |   8 points |
    /// | 5 |   1,438,977 |  12.5×  |  16 points |
    /// | 6 |   1,210,663 |  14.9×  |  32 points |
    /// | 8 |     965,955 |  18.7×  | 128 points |
    /// |10 |     823,037 |  21.9×  | 512 points |
    /// |11 |     816,873 |  22.1×  |1024 points |
    ///
    /// The gain flattens past `w ≈ 11`, where the mux over `2^(w−1)` table entries starts to cost
    /// more than the point addition it saves. What bounds the width in practice is the table, which
    /// holds `2^(w−1)` points per window: 52 KiB at `w = 5` against 1,536 KiB at `w = 11`.
    pub fn mul_secret_scalar<B: Backend>(
        self,
        scalar: WordRef<B, W, N>,
    ) -> CurvePointRef<B, W, N, C> {
        let curve = self.curve;
        let mut tables = ComputedWindowTables::new(self, DEFAULT_COMB_WINDOW_BITS);
        return curve.mul_secret_scalar(scalar, &mut tables);
    }
}

/// Oblivious mux of one constant [MontgomeryWord] out of `2^bits.len()` by the given secret bits
/// (little-endian: `bits[0]` is the low bit of the index).
pub(crate) fn select_const_coord<B: Backend, W: Word, const N: usize, M: FieldRep<W, N>>(
    bits: &[BooleanWordRef<B>],
    consts: &[MontgomeryWord<W, N, M>],
) -> MontgomeryWordRef<B, W, N, M> {
    // Hard assert (not debug-only): a mis-sized table from a custom `WindowTables` impl would
    // otherwise silently mux the wrong constant into this soundness-critical selection in release.
    assert_eq!(consts.len(), 1 << bits.len());
    // First level selects between pairs of constants by the low bit.
    let mut layer: Vec<MontgomeryWordRef<B, W, N, M>> = consts
        .chunks(2)
        .map(|pair| {
            bits[0]
                .clone()
                .montgomery_select_const_const(pair[1], pair[0])
        })
        .collect();
    // Higher levels mux the (now variable) partial results by the higher bits.
    for bit in bits.iter().skip(1) {
        layer = layer
            .chunks(2)
            .map(|pair| {
                bit.clone()
                    .montgomery_select(pair[1].clone(), pair[0].clone())
            })
            .collect();
    }
    return layer.into_iter().next().expect("non-empty mux");
}

/// Oblivious select of one signed multiple of the base from a window's affine odd-multiple table.
fn select_signed_point<B: Backend, W: Word, const N: usize, C: Curve<W, N>>(
    index_bits: &[BooleanWordRef<B>],
    sign_neg: BooleanWordRef<B>,
    table: &[[MontgomeryWord<W, N, C::P>; 3]],
    curve: C,
) -> CurvePointRef<B, W, N, C> {
    let xs: Vec<MontgomeryWord<W, N, C::P>> = table.iter().map(|c| c[0]).collect();
    let ys: Vec<MontgomeryWord<W, N, C::P>> = table.iter().map(|c| c[1]).collect();
    let x = select_const_coord(index_bits, &xs);
    let y = select_const_coord(index_bits, &ys);
    let y = sign_neg.montgomery_select(-y.clone(), y);
    return CurvePointRef::_affine(x, y, curve);
}

/// Default comb window width for [`CurvePoint::mul_secret_scalar`] — a strong reduction in
/// nonlinear gates with a small per-window table (`2^(w−1)` affine points, ~2 KiB at `w = 5`),
/// suitable for a memory- and flash-constrained on-device prover: at this width the base-point
/// table fits the device's app flash.
pub const DEFAULT_COMB_WINDOW_BITS: usize = 5;

/// Comb window width for a host prover with memory to spare, the optimum for a 256-bit scalar.
///
/// Widths above this buy little — the mux over `2^(w−1)` table entries starts to cost more than the
/// point addition it saves — while the table grows as `2^(w−1)` per window. Pair it with
/// [`PrecomputedWindowTables`], whose table is 464 KiB at this width against 52 KiB at
/// [`DEFAULT_COMB_WINDOW_BITS`].
pub const HOST_COMB_WINDOW_BITS: usize = 9;

/// The number of windows the signed-digit comb ([`Curve::mul_secret_scalar`]) consumes a
/// `width`-bit scalar in, at window width `window_bits`.
pub const fn comb_window_count(width: usize, window_bits: usize) -> usize {
    return width / window_bits + 1;
}

/// Supplies the per-window point tables for fixed-base comb scalar multiplication
/// ([`Curve::mul_secret_scalar`] / [`CurvePoint::mul_secret_scalar`]).
pub trait WindowTables<W: Word, const N: usize, C: Curve<W, N>> {
    /// The window width `w` in bits; the scalar is consumed `w` bits at a time.
    fn window_bits(&self) -> usize;

    /// The table for window `k`: entry `idx` is the affine point `(2·idx+1) · 2^{window_bits·k} ·
    /// base`.
    fn window(&mut self, k: usize) -> &[[MontgomeryWord<W, N, C::P>; 3]];
}

/// The default [`WindowTables`]: builds each window's table on demand by native point arithmetic —
/// exactly what the comb did inline before.
#[derive(Debug, Clone)]
pub struct ComputedWindowTables<W: Word, const N: usize, C: Curve<W, N>> {
    curve: C,
    base: CurvePoint<W, N, C>,
    base_k: CurvePoint<W, N, C>,
    next_k: usize,
    window_bits: usize,
    buf: Vec<[MontgomeryWord<W, N, C::P>; 3]>,
}

impl<W: Word, const N: usize, C: Curve<W, N>> ComputedWindowTables<W, N, C> {
    /// A comb-table source for `base`, with the given window width.
    pub fn new(base: CurvePoint<W, N, C>, window_bits: usize) -> Self {
        return Self {
            curve: base.curve(),
            base,
            base_k: base,
            next_k: 0,
            window_bits,
            buf: Vec::with_capacity(1usize << window_bits.saturating_sub(1)),
        };
    }
}

impl<W: Word, const N: usize, C: Curve<W, N>> WindowTables<W, N, C>
    for ComputedWindowTables<W, N, C>
{
    #[inline]
    fn window_bits(&self) -> usize {
        return self.window_bits;
    }

    fn window(&mut self, k: usize) -> &[[MontgomeryWord<W, N, C::P>; 3]] {
        let width = W::WIDTH * N;
        if k == 0 {
            self.base_k = self.base;
            self.next_k = 0;
        }
        assert_eq!(
            k, self.next_k,
            "windows must be requested in ascending order (or restarting from 0)"
        );
        assert!(
            k < comb_window_count(width, self.window_bits),
            "window index past the last window of the scalar"
        );
        let half = 1usize << (self.window_bits - 1);

        // Rebuild the odd multiples T_k[j] = (2j+1) · base_k, j = 0 .. 2^(w−1), into the reused
        // buffer, then normalise them to affine (z = 1) for mixed addition. Every multiple is a
        // nonzero, non-infinity point (its coefficient is below the group order times a small odd
        // factor and never a multiple of it), so the batched inversion never divides by zero.
        self.buf.clear();
        let two_base_k = self.base_k.double();
        let mut acc = self.base_k;
        for j in 0..half {
            if j > 0 {
                acc = acc + two_base_k;
            }
            self.buf.push(acc.coords());
        }
        normalize_affine::<W, N, C>(&mut self.buf, self.curve);

        // Advance base_k to 2^{window_bits·(k+1)} · base for the next window.
        for _ in 0..self.window_bits {
            self.base_k = self.base_k.double();
        }
        self.next_k = k + 1;
        return &self.buf;
    }
}

/// A RAM-resident [`WindowTables`]: every window's table built once, up front, and held for the
/// lifetime of the source. Random access — windows may be requested in any order, any number of
/// times, and by several scalar multiplications concurrently.
///
/// This is the host counterpart of [`ComputedWindowTables`], which rebuilds a window's `2^(w−1)`
/// multiples by native point arithmetic on *every* request. That rebuild is not incidental: a
/// circuit pass requests every window once, and a proof runs two passes per repetition, so the
/// tables are rebuilt `2 · repetitions` times over. Precomputing collapses that to a single build,
/// and normalises the whole table to affine with **one** field inversion instead of one per window.
///
/// The cost is memory. The table holds `2^(w−1)` points per window and
/// [`comb_window_count`] windows — for a 256-bit scalar, 52 KiB at `w = 5`, 464 KiB at
/// `w = 9` ([`HOST_COMB_WINDOW_BITS`]), and 1,536 KiB at `w = 11` — so this source is for hosts;
/// constrained provers should keep the on-demand [`ComputedWindowTables`].
#[derive(Debug, Clone)]
pub struct PrecomputedWindowTables<W: Word, const N: usize, C: Curve<W, N>> {
    window_bits: usize,
    num_windows: usize,
    /// All windows concatenated: window `k` occupies `[k · 2^(w−1) .. (k+1) · 2^(w−1))`.
    points: Vec<[MontgomeryWord<W, N, C::P>; 3]>,
}

impl<W: Word, const N: usize, C: Curve<W, N>> PrecomputedWindowTables<W, N, C> {
    /// Builds the full comb table for `base` at the given window width.
    pub fn new(base: CurvePoint<W, N, C>, window_bits: usize) -> Self {
        assert!(
            window_bits >= 2,
            "window width must be at least 2 bits, got {window_bits}"
        );
        let curve = base.curve();
        let num_windows = comb_window_count(W::WIDTH * N, window_bits);
        let half = 1usize << (window_bits - 1);
        let mut points = Vec::with_capacity(num_windows * half);
        let mut base_k = base;
        for _ in 0..num_windows {
            // Odd multiples T_k[j] = (2j+1) · base_k, j = 0 .. 2^(w−1). Every one is a nonzero,
            // non-infinity point (its coefficient is below the group order times a small odd factor
            // and never a multiple of it), so the batched inversion never divides by zero.
            let two_base_k = base_k.double();
            let mut acc = base_k;
            for j in 0..half {
                if j > 0 {
                    acc = acc + two_base_k;
                }
                points.push(acc.coords());
            }
            for _ in 0..window_bits {
                base_k = base_k.double();
            }
        }
        normalize_affine::<W, N, C>(&mut points, curve);
        return Self {
            window_bits,
            num_windows,
            points,
        };
    }

    /// The number of windows held, [`comb_window_count`] for the scalar width and window width.
    pub fn num_windows(&self) -> usize {
        return self.num_windows;
    }

    /// The total number of affine points held, across all windows.
    pub fn len(&self) -> usize {
        return self.points.len();
    }

    /// Whether the table is empty (it never is: there is always at least one window).
    pub fn is_empty(&self) -> bool {
        return self.points.is_empty();
    }
}

impl<W: Word, const N: usize, C: Curve<W, N>> WindowTables<W, N, C>
    for PrecomputedWindowTables<W, N, C>
{
    #[inline]
    fn window_bits(&self) -> usize {
        return self.window_bits;
    }

    fn window(&mut self, k: usize) -> &[[MontgomeryWord<W, N, C::P>; 3]] {
        assert!(
            k < self.num_windows,
            "window index past the last window of the scalar"
        );
        let half = 1usize << (self.window_bits - 1);
        return &self.points[k * half..(k + 1) * half];
    }
}


/// Batched normalisation of Jacobian points to affine (`z = 1`), in place.
fn normalize_affine<W: Word, const N: usize, C: Curve<W, N>>(
    buf: &mut [[MontgomeryWord<W, N, C::P>; 3]],
    curve: C,
) {
    let field = curve.p();
    let one = field.one_word();
    let mut prefix = Vec::with_capacity(buf.len());
    let mut running = one;
    for entry in buf.iter() {
        prefix.push(running);
        running = running * entry[2];
    }
    let mut running_inv =
        MontgomeryWord::from_inner(field.invert_const(running.into_inner()), field);
    for i in (0..buf.len()).rev() {
        let z_inv = running_inv * prefix[i];
        running_inv = running_inv * buf[i][2];
        let z_inv_sq = z_inv * z_inv;
        let z_inv_cub = z_inv_sq * z_inv;
        buf[i][0] = buf[i][0] * z_inv_sq;
        buf[i][1] = buf[i][1] * z_inv_cub;
        buf[i][2] = one;
    }
}

impl<W: Word, const N: usize, C: Curve<W, N>> Neg for CurvePoint<W, N, C> {
    type Output = Self;
    /// Point negation on the [Curve].
    fn neg(self) -> Self::Output {
        let (x, y, z, curve) = self.destructure();
        return Self::_inf_or_jacobian(z.is_zero(), x, -y, z, curve);
    }
}

impl<W: Word, const N: usize, C: Curve<W, N>> Add for CurvePoint<W, N, C> {
    type Output = Self;
    /// Point addition on the [Curve].
    fn add(self, rhs: Self) -> Self::Output {
        assert_eq!(
            self.curve, rhs.curve,
            "Cannot add points on different curves."
        );
        if self.is_inf() {
            return rhs;
        }
        if rhs.is_inf() {
            return self;
        }
        let (x1, y1, z1, curve) = self.destructure();
        let (x2, y2, z2, _) = rhs.destructure();
        let z1z1 = z1 * z1;
        let z2z2 = z2 * z2;
        let u1 = x1 * z2z2;
        let u2 = x2 * z1z1;
        let s1 = y1 * z2z2 * z2;
        let s2 = y2 * z1z1 * z1;
        if u1 == u2 {
            if s1 == s2 {
                return self.double();
            } else {
                return curve.zero();
            }
        }
        let h = u2 - u1;
        let h_dbl = h + h;
        let h_sq_quad = h_dbl * h_dbl;
        let h_cub_quad = h_sq_quad * h;
        let r = s2 + s2 - (s1 + s1);
        let v = u1 * h_sq_quad;
        let res_x = r * r - h_cub_quad - v - v;
        let t = s1 * h_cub_quad;
        let res_y = r * (v - res_x) - t - t;
        let z_sum = z1 + z2;
        let res_z = h * (z_sum * z_sum - z1z1 - z2z2);
        return Self::_jacobian(res_x, res_y, res_z, curve);
    }
}

impl<W: Word, const N: usize, C: Curve<W, N>> AddAssign for CurvePoint<W, N, C> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<W: Word, const N: usize, C: Curve<W, N>> Sub for CurvePoint<W, N, C> {
    type Output = Self;
    /// Point subtraction on the [Curve].
    fn sub(self, rhs: Self) -> Self::Output {
        return self + (-rhs);
    }
}

impl<W: Word, const N: usize, C: Curve<W, N>> SubAssign for CurvePoint<W, N, C> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<W: Word, const N: usize, C: Curve<W, N>, U: WordLike<W, N>> Mul<U> for CurvePoint<W, N, C> {
    type Output = Self;
    /// Point multiplication by a scalar on the [Curve].
    fn mul(self, rhs: U) -> Self::Output {
        let rhs = rhs.to_word();
        let mut res = self.curve.zero();
        let mut addend = self;
        rhs.map_bits(|bit| {
            if bit {
                res += addend;
            }
            addend = addend.double();
        });
        return res;
    }
}
impl<W: Word, const N: usize, C: Curve<W, N>, U: WordLike<W, N>> MulAssign<U>
    for CurvePoint<W, N, C>
{
    fn mul_assign(&mut self, rhs: U) {
        *self = *self * rhs;
    }
}

/// Reference to a point on an elliptic curve in short Weierstrass form, in Jacobian representation,
/// with coordinates in Montgomery form.
#[derive(Debug)]
pub struct CurvePointRef<B: Backend, W: Word, const N: usize, C: Curve<W, N>> {
    x: MontgomeryWordRef<B, W, N, C::P>,
    y: MontgomeryWordRef<B, W, N, C::P>,
    z: MontgomeryWordRef<B, W, N, C::P>,
    curve: C,
}

impl<B: Backend, W: Word, const N: usize, C: Curve<W, N>> Clone for CurvePointRef<B, W, N, C> {
    fn clone(&self) -> Self {
        return Self {
            x: self.x.clone(),
            y: self.y.clone(),
            z: self.z.clone(),
            curve: self.curve,
        };
    }
}

impl<B: Backend, W: Word, const N: usize, C: Curve<W, N>> CurvePointRef<B, W, N, C> {
    /// Helper constructor for points in affine representation.
    fn _affine(
        x: MontgomeryWordRef<B, W, N, C::P>,
        y: MontgomeryWordRef<B, W, N, C::P>,
        curve: C,
    ) -> Self {
        let one = x.clone().into_const(CompositeWord::ONE);
        return Self {
            x,
            y,
            z: one,
            curve,
        };
    }

    /// Helper constructor for points in Jacobian representation.
    fn _jacobian(
        x: MontgomeryWordRef<B, W, N, C::P>,
        y: MontgomeryWordRef<B, W, N, C::P>,
        z: MontgomeryWordRef<B, W, N, C::P>,
        curve: C,
    ) -> Self {
        return Self { x, y, z, curve };
    }

    /// Helper constructor to conditionally construct either the infinite point or
    /// a Jacobian point, based on a boolean flag.
    fn _inf_or_jacobian(
        is_inf: BooleanWordRef<B>,
        x: MontgomeryWordRef<B, W, N, C::P>,
        y: MontgomeryWordRef<B, W, N, C::P>,
        z: MontgomeryWordRef<B, W, N, C::P>,
        curve: C,
    ) -> Self {
        let x = is_inf.clone().montgomery_select(x.clone().into_zero(), x);
        let y = is_inf
            .clone()
            .montgomery_select(y.clone().into_const(CompositeWord::ONE), y);
        let z = is_inf.clone().montgomery_select(z.clone().into_zero(), z);
        return Self { x, y, z, curve };
    }

    /// Get the coordinates of the point as an array of references.
    pub fn coords(&self) -> [&MontgomeryWordRef<B, W, N, C::P>; 3] {
        return [&self.x, &self.y, &self.z];
    }

    /// Convert the point to affine representation.
    pub fn into_coords(self) -> [MontgomeryWordRef<B, W, N, C::P>; 3] {
        return [self.x, self.y, self.z];
    }

    /// Get the curve that the point is on.
    pub fn curve(&self) -> C {
        return self.curve;
    }

    /// Destructure the point into its coordinates and curve.
    pub fn destructure(
        self,
    ) -> (
        MontgomeryWordRef<B, W, N, C::P>,
        MontgomeryWordRef<B, W, N, C::P>,
        MontgomeryWordRef<B, W, N, C::P>,
        C,
    ) {
        return (self.x, self.y, self.z, self.curve);
    }

    /// Consumes the point and returns an infinite point on the curve.
    pub fn into_inf(self) -> Self {
        let (x, y, z, curve) = self.destructure();
        let x = x.into_zero();
        let y = y.into_const(CompositeWord::ONE);
        let z = z.into_zero();
        return Self { x, y, z, curve };
    }

    /// Check if the point is in affine representation, i.e. if `z == 1`.
    pub fn is_affine(&self) -> BooleanWordRef<B> {
        return self.z.clone().eq_const(self.curve.p().one_word());
    }

    /// Check if the point is the infinite point, i.e. if `z == 0`.
    pub fn is_inf(&self) -> BooleanWordRef<B> {
        return self.z.clone().is_zero();
    }

    /// Convert the point to affine representation.
    pub fn to_affine(self) -> Self {
        let is_inf = self.is_inf();
        let (x, y, z, curve) = self.destructure();
        let z_inv = z.clone().inv();
        let z_inv_sq = z_inv.clone() * z_inv.clone();
        let x_affine = x * z_inv_sq.clone();
        let y_affine = y * z_inv_sq * z_inv;
        let z_affine = z.into_const(CompositeWord::ONE);
        return Self::_inf_or_jacobian(is_inf, x_affine, y_affine, z_affine, curve);
    }

    /// Point doubling on the [Curve].
    pub fn double(self) -> Self {
        let (x, y, z, curve) = self.destructure();
        let is_inf = z.clone().is_zero() | y.clone().is_zero();
        let yy = y.clone() * y.clone();
        let xyy = x.clone() * yy.clone();
        let xx = x.clone() * x;
        let xyy2 = xyy.clone() + xyy;
        let s = xyy2.clone() + xyy2;
        let m = xx.clone() + xx.clone() + xx;
        let s2 = s.clone() + s.clone();
        let res_x = m.clone() * m.clone() - s2;
        let yyyy = yy.clone() * yy;
        let yyyy2 = yyyy.clone() + yyyy;
        let yyyy4 = yyyy2.clone() + yyyy2;
        let yyyy8 = yyyy4.clone() + yyyy4;
        let res_y = m * (s - res_x.clone()) - yyyy8;
        let yz = y * z;
        let res_z = yz.clone() + yz;
        return Self::_inf_or_jacobian(is_inf, res_x, res_y, res_z, curve);
    }

    /// Mixed addition of an affine point into this Jacobian point — **generic case only**.
    fn madd(self, rhs: Self) -> Self {
        let (x1, y1, z1, curve) = self.destructure();
        let (x2, y2, _z2, _) = rhs.destructure();
        let z1z1 = z1.clone() * z1.clone();
        let u2 = x2 * z1z1.clone();
        let s2 = y2 * z1.clone() * z1z1.clone();
        let h = u2 - x1.clone();
        let hh = h.clone() * h.clone();
        let hh2 = hh.clone() + hh.clone();
        let i = hh2.clone() + hh2;
        let j = h.clone() * i.clone();
        let s2_y1 = s2 - y1.clone();
        let r = s2_y1.clone() + s2_y1;
        let v = x1 * i;
        let res_x = r.clone() * r.clone() - j.clone() - v.clone() - v.clone();
        let y1j = y1 * j;
        let res_y = r * (v - res_x.clone()) - y1j.clone() - y1j;
        let z1h = z1.clone() + h.clone();
        let res_z = z1h.clone() * z1h - z1z1 - hh;
        return Self::_jacobian(res_x, res_y, res_z, curve);
    }

    /// Check if two points are equal, without affine conversion.
    ///
    /// Branch-less (data-oblivious) analogue of [CurvePoint::eq]: works directly on the Jacobian
    /// coordinates and returns a [BooleanWordRef] rather than branching on secret values. Two
    /// points are equal iff (a) both are the point at infinity (`z == 0`), or (b) both are finite
    /// and their affine coordinates coincide, i.e. `x1·z2² == x2·z1²` and `y1·z2³ == y2·z1³`.
    pub fn eq(self, rhs: Self) -> BooleanWordRef<B> {
        let (x1, y1, z1, curve1) = self.destructure();
        let (x2, y2, z2, curve2) = rhs.destructure();
        assert_eq!(curve1, curve2, "Cannot compare points on different curves.");
        let inf1 = z1.clone().is_zero();
        let inf2 = z2.clone().is_zero();
        let z1z1 = z1.clone() * z1.clone();
        let z2z2 = z2.clone() * z2.clone();
        let eqx = (x1 * z2z2.clone()).eq(x2 * z1z1.clone());
        let eqy = (y1 * z2z2 * z2).eq(y2 * z1z1 * z1);
        let both_inf = inf1.clone() & inf2.clone();
        let both_finite = !inf1 & !inf2;
        // equal iff both at infinity, or both finite with matching affine coordinates.
        return both_inf | (both_finite & eqx & eqy);
    }

    /// Check if two points are not equal, without affine conversion.
    pub fn ne(self, rhs: Self) -> BooleanWordRef<B> {
        return !self.eq(rhs);
    }
}

impl<B: Backend, W: Word, const N: usize, C: Curve<W, N>> Neg for CurvePointRef<B, W, N, C> {
    type Output = Self;
    /// Point negation on the [Curve].
    fn neg(self) -> Self::Output {
        let (x, y, z, curve) = self.destructure();
        return Self::_inf_or_jacobian(z.clone().is_zero(), x, -y, z, curve);
    }
}

impl<B: Backend, W: Word, const N: usize, C: Curve<W, N>> Add for CurvePointRef<B, W, N, C> {
    type Output = Self;
    /// Point addition on the [Curve].
    fn add(self, rhs: Self) -> Self::Output {
        assert_eq!(
            self.curve, rhs.curve,
            "Cannot add points on different curves."
        );
        let branch0 = self.clone().is_inf();
        let branch1 = rhs.clone().is_inf();
        let [res_t_x, res_t_y, res_t_z] = rhs.clone().into_coords();
        let [res_ft_x, res_ft_y, res_ft_z] = self.clone().into_coords();
        let [res_fftt_x, res_fftt_y, res_fftt_z] = self.clone().double().into_coords();
        let [res_fftf_x, res_fftf_y, res_fftf_z] = self.clone().into_inf().into_coords();
        let (x1, y1, z1, curve) = self.destructure();
        let (x2, y2, z2, _) = rhs.destructure();
        let z1z1 = z1.clone() * z1.clone();
        let z2z2 = z2.clone() * z2.clone();
        let u1 = x1 * z2z2.clone();
        let u2 = x2 * z1z1.clone();
        let s1 = y1 * z2z2.clone() * z2.clone();
        let s2 = y2 * z1z1.clone() * z1.clone();
        let branch2 = u1.clone().eq(u2.clone());
        let branch3 = s1.clone().eq(s2.clone());
        let h = u2 - u1.clone();
        let h_dbl = h.clone() + h.clone();
        let h_sq_quad = h_dbl.clone() * h_dbl;
        let h_cub_quad = h_sq_quad.clone() * h.clone();
        let r = s2.clone() + s2 - (s1.clone() + s1.clone());
        let v = u1.clone() * h_sq_quad;
        let res_fff_x = r.clone() * r.clone() - h_cub_quad.clone() - v.clone() - v.clone();
        let t = s1 * h_cub_quad;
        let res_fff_y = r * (v - res_fff_x.clone()) - t.clone() - t;
        let z_sum = z1 + z2;
        let res_fff_z = h * (z_sum.clone() * z_sum - z1z1 - z2z2);
        return branch0.point_select(
            CurvePointRef {
                x: res_t_x,
                y: res_t_y,
                z: res_t_z,
                curve,
            },
            branch1.point_select(
                CurvePointRef {
                    x: res_ft_x,
                    y: res_ft_y,
                    z: res_ft_z,
                    curve,
                },
                branch2.point_select(
                    branch3.point_select(
                        CurvePointRef {
                            x: res_fftt_x,
                            y: res_fftt_y,
                            z: res_fftt_z,
                            curve,
                        },
                        CurvePointRef {
                            x: res_fftf_x,
                            y: res_fftf_y,
                            z: res_fftf_z,
                            curve,
                        },
                    ),
                    CurvePointRef {
                        x: res_fff_x,
                        y: res_fff_y,
                        z: res_fff_z,
                        curve,
                    },
                ),
            ),
        );
    }
}

impl<B: Backend, W: Word, const N: usize, C: Curve<W, N>> AddAssign for CurvePointRef<B, W, N, C> {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.clone() + rhs;
    }
}

impl<B: Backend, W: Word, const N: usize, C: Curve<W, N>> Sub for CurvePointRef<B, W, N, C> {
    type Output = Self;
    /// Point subtraction on the [Curve].
    fn sub(self, rhs: Self) -> Self::Output {
        return self + (-rhs);
    }
}

impl<B: Backend, W: Word, const N: usize, C: Curve<W, N>> SubAssign for CurvePointRef<B, W, N, C> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.clone() - rhs;
    }
}

impl<B: Backend, W: Word, const N: usize, C: Curve<W, N>> Mul<CompositeWord<W, N>>
    for CurvePointRef<B, W, N, C>
{
    type Output = Self;
    /// Point multiplication by a **public** (cleartext) scalar on the [Curve].
    fn mul(self, rhs: CompositeWord<W, N>) -> Self::Output {
        let mut res = self.clone().into_inf();
        let mut addend = self;
        rhs.map_bits(|bit| {
            if bit {
                res += addend.clone();
            }
            addend = addend.clone().double();
        });
        return res;
    }
}
impl<B: Backend, W: Word, const N: usize, C: Curve<W, N>> MulAssign<CompositeWord<W, N>>
    for CurvePointRef<B, W, N, C>
{
    fn mul_assign(&mut self, rhs: CompositeWord<W, N>) {
        *self = self.clone() * rhs;
    }
}

impl<B: Backend, W: Word, const N: usize, C: Curve<W, N>> Mul<WordRef<B, W, N>>
    for CurvePointRef<B, W, N, C>
{
    type Output = Self;
    /// Point multiplication by a **secret** (circuit-value) scalar on the [Curve].
    fn mul(self, rhs: WordRef<B, W, N>) -> Self::Output {
        let mut res = self.clone().into_inf();
        let mut addend = self;
        rhs.map_bits(|bit| {
            res = bit.point_select(res.clone() + addend.clone(), res.clone());
            addend = addend.clone().double();
        });
        return res;
    }
}
impl<B: Backend, W: Word, const N: usize, C: Curve<W, N>> MulAssign<WordRef<B, W, N>>
    for CurvePointRef<B, W, N, C>
{
    fn mul_assign(&mut self, rhs: WordRef<B, W, N>) {
        *self = self.clone() * rhs;
    }
}

/// Helper trait implementing curve point selection by a [BooleanWordRef].
pub trait PointBooleanWordRefSelector<B: Backend, W: Word, const N: usize, C: Curve<W, N>> {
    fn point_select(
        self,
        then: CurvePointRef<B, W, N, C>,
        else_: CurvePointRef<B, W, N, C>,
    ) -> CurvePointRef<B, W, N, C>;
}

impl<B: Backend, W: Word, const N: usize, C: Curve<W, N>> PointBooleanWordRefSelector<B, W, N, C>
    for BooleanWordRef<B>
{
    /// Select between two curve points by a [BooleanWordRef].
    fn point_select(
        self,
        then: CurvePointRef<B, W, N, C>,
        else_: CurvePointRef<B, W, N, C>,
    ) -> CurvePointRef<B, W, N, C> {
        assert_eq!(
            then.curve, else_.curve,
            "Cannot select between points on different curves."
        );
        let (x1, y1, z1, curve) = then.destructure();
        let (x2, y2, z2, _) = else_.destructure();
        let x = self.clone().montgomery_select(x1, x2);
        let y = self.clone().montgomery_select(y1, y2);
        let z = self.montgomery_select(z1, z2);
        return CurvePointRef { x, y, z, curve };
    }
}

/// Helper trait implementing point allocation for a [Frontend].
pub trait PointFrontendIO<B: Backend, W: Word, const N: usize, C: Curve<W, N>> {
    /// Variant of [Frontend::input] for curve points.
    fn point_input(&self, in_: CurvePoint<W, N, C>) -> CurvePointRef<B, W, N, C>;

    /// Variant of [Frontend::alloc] for curve points.
    fn point_alloc(&self, in_: CurvePoint<W, N, C>) -> CurvePointRef<B, W, N, C>;

    /// Variant of [Frontend::output] for curve points, outputting in affine representation.
    fn point_output_affine(&self, out: CurvePointRef<B, W, N, C>);

    /// Variant of [Frontend::output] for curve points, outputting in Jacobian representation.
    fn point_output_jacobian(&self, out: CurvePointRef<B, W, N, C>);
}

impl<B: Backend, W: Word, const N: usize, C: Curve<W, N>> PointFrontendIO<B, W, N, C>
    for Frontend<B>
{
    fn point_input(&self, in_: CurvePoint<W, N, C>) -> CurvePointRef<B, W, N, C> {
        let (x, y, z, curve) = in_.destructure();
        let x = self.montgomery_input(x);
        let y = self.montgomery_input(y);
        let z = self.montgomery_input(z);
        return CurvePointRef { x, y, z, curve };
    }

    fn point_alloc(&self, in_: CurvePoint<W, N, C>) -> CurvePointRef<B, W, N, C> {
        let (x, y, z, curve) = in_.destructure();
        let x = self.montgomery_alloc(x);
        let y = self.montgomery_alloc(y);
        let z = self.montgomery_alloc(z);
        return CurvePointRef { x, y, z, curve };
    }

    fn point_output_affine(&self, out: CurvePointRef<B, W, N, C>) {
        let (x, y, _, _) = out.to_affine().destructure();
        self.montgomery_output(x);
        self.montgomery_output(y);
    }

    fn point_output_jacobian(&self, out: CurvePointRef<B, W, N, C>) {
        let (x, y, z, _) = out.destructure();
        self.montgomery_output(x);
        self.montgomery_output(y);
        self.montgomery_output(z);
    }
}
