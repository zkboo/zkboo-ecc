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
use zkboo_modular::montgomery::{
    MontgomeryBooleanWordRefSelector, MontgomeryFrontendIO, MontgomeryMod, MontgomeryWord,
    MontgomeryWordRef,
};

/// An elliptic curve in short Weierstrass form, defined by the equation `y^2 = x^3 + ax + b`
/// over a prime field, with coefficients in Montgomery form.
pub trait Curve<W: Word, const N: usize>: Clone + Copy + PartialEq + Eq + Debug {
    type P: MontgomeryMod<W, N>;

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
    pub fn to_affine(self) -> Self {
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

    /// Fixed-base scalar multiplication by a **secret** (circuit-value) scalar, data-oblivious.
    ///
    /// Because this base point is a public constant, every multiple `2^i · self` is known at
    /// circuit-build time. Decomposing the scalar into `w`-bit windows, `d·self = Σ_k T_k[w_k]`
    /// where `T_k[j] = j · 2^{w·k} · self` is a build-time table, so the in-circuit work is just
    /// `⌈WIDTH/w⌉` oblivious table selects and additions — and **no in-circuit doublings** (the
    /// dominant cost of the generic double-and-add ladder). For secp256k1 this is roughly an
    /// order of magnitude cheaper than [`CurvePointRef::mul`] by a secret scalar.
    ///
    /// Data-oblivious: the table selects iterate every window position and use the secret window
    /// bits only to drive `montgomery_select`, so the gate sequence is independent of the scalar.
    ///
    /// The window width [`W_BITS`](Self::mul_secret_scalar) trades nonlinear gates against the
    /// per-window table size (`2^w` points, rebuilt each window, so it bounds peak memory).
    /// Measured for a full secp256k1 `d·G` (vs. 39.3M nonlinear and_msgs for the ladder):
    ///
    /// | w | nl and_msgs | speedup | peak table |
    /// |---|------------:|--------:|-----------:|
    /// | 4 |   7,528,311 |   5.2×  |  16 points |
    /// | 6 |   5,088,909 |   7.7×  |  64 points |
    /// | 8 |   3,866,423 |  10.2×  | 256 points |
    /// |10 |   3,373,355 |  11.6×  |1024 points |
    ///
    /// `w = 6` is the default: a strong reduction with a small (~6 KiB) table, suitable for the
    /// memory-constrained on-device prover. Raise it for host proving where memory is ample.
    pub fn mul_secret_scalar<B: Backend>(
        self,
        scalar: WordRef<B, W, N>,
    ) -> CurvePointRef<B, W, N, C> {
        const W_BITS: usize = 6;
        let width = W::WIDTH * N;
        let num_windows = width.div_ceil(W_BITS);
        let curve = self.curve;

        let mut res: Option<CurvePointRef<B, W, N, C>> = None;
        // `base_k` is `2^{W_BITS·k} · self`, advanced by `W_BITS` doublings per window.
        let mut base_k = self;
        for k in 0..num_windows {
            let bits_in_window = core::cmp::min(W_BITS, width - k * W_BITS);
            // Build the window table T_k[j] = j · base_k incrementally (native, build-time):
            // T_k[0] = ∞, T_k[j] = T_k[j-1] + base_k.
            let mut table: Vec<[MontgomeryWord<W, N, C::P>; 3]> =
                Vec::with_capacity(1usize << bits_in_window);
            let mut acc = curve.zero();
            table.push(acc.coords());
            for _ in 1..(1usize << bits_in_window) {
                acc = acc + base_k;
                table.push(acc.coords());
            }
            // Oblivious select of T_k[w_k] by the secret window bits, then accumulate.
            let window_bits: Vec<BooleanWordRef<B>> = (0..bits_in_window)
                .map(|i| scalar.clone().bit_at(k * W_BITS + i))
                .collect();
            let selected = select_const_point(&window_bits, &table, curve);
            res = Some(match res {
                None => selected,
                Some(r) => r + selected,
            });
            for _ in 0..W_BITS {
                base_k = base_k.double();
            }
        }
        // `width >= 1`, so `num_windows >= 1` and `res` is always set.
        return res.expect("at least one window");
    }
}

/// Oblivious mux of one constant [MontgomeryWord] out of `2^bits.len()` by the given secret bits
/// (little-endian: `bits[0]` is the low bit of the index).
fn select_const_coord<B: Backend, W: Word, const N: usize, M: MontgomeryMod<W, N>>(
    bits: &[BooleanWordRef<B>],
    consts: &[MontgomeryWord<W, N, M>],
) -> MontgomeryWordRef<B, W, N, M> {
    debug_assert_eq!(consts.len(), 1 << bits.len());
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
            .map(|pair| bit.clone().montgomery_select(pair[1].clone(), pair[0].clone()))
            .collect();
    }
    return layer.into_iter().next().expect("non-empty mux");
}

/// Oblivious select of one constant curve point (its three coordinates) out of a window table.
fn select_const_point<B: Backend, W: Word, const N: usize, C: Curve<W, N>>(
    bits: &[BooleanWordRef<B>],
    table: &[[MontgomeryWord<W, N, C::P>; 3]],
    curve: C,
) -> CurvePointRef<B, W, N, C> {
    let xs: Vec<MontgomeryWord<W, N, C::P>> = table.iter().map(|c| c[0]).collect();
    let ys: Vec<MontgomeryWord<W, N, C::P>> = table.iter().map(|c| c[1]).collect();
    let zs: Vec<MontgomeryWord<W, N, C::P>> = table.iter().map(|c| c[2]).collect();
    return CurvePointRef::_jacobian(
        select_const_coord(bits, &xs),
        select_const_coord(bits, &ys),
        select_const_coord(bits, &zs),
        curve,
    );
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
