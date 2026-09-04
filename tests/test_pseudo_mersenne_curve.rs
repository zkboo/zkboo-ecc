// SPDX-License-Identifier: LGPL-3.0-or-later

//! Validates the pseudo-Mersenne secp256k1 curve [Secp256k1PM] against the trusted Montgomery
//! curve [Secp256k1]: both compute the same group, so `d·G` must agree as curve points. The
//! native cross-check (cheap, no circuit) decodes both representations to canonical integers and
//! compares projectively; a circuit check confirms the fixed-base comb agrees with the native PM
//! scalar multiplication.

use dashu_int::UBig;
use zkboo::{
    backend::{Backend, Frontend},
    circuit::Circuit,
    executor::{OwnedFlexibleWordPool, exec},
    word::{CompositeWord, Words},
};
use zkboo_ecc::montgomery::{Curve, CurvePoint};
use zkboo_ecc::secp256k1::{Secp256k1, Secp256k1PM};
use zkboo_modular::montgomery::MontgomeryMod;
use zkboo::executor::ExecOptions;

type WP = OwnedFlexibleWordPool<usize>;

fn to_ubig(w: CompositeWord<u64, 4>) -> UBig {
    let mut v = UBig::ZERO;
    for &limb in w.to_le_words().iter().rev() {
        v = (v << 64) + UBig::from(limb);
    }
    v
}
fn p() -> UBig {
    to_ubig(Secp256k1.p().n())
}

/// Canonical (x, y, z) of a curve point, decoded out of its field representation.
fn coords<C: Curve<u64, 4>>(pt: &CurvePoint<u64, 4, C>) -> (UBig, UBig, UBig) {
    let [x, y, z] = pt.coords();
    (to_ubig(x.value()), to_ubig(y.value()), to_ubig(z.value()))
}

/// Projective equality of two Jacobian points over the same prime: x1·z2² ≡ x2·z1² and
/// y1·z2³ ≡ y2·z1³ (mod p), with both-infinity handled.
fn jacobian_eq(a: (UBig, UBig, UBig), b: (UBig, UBig, UBig)) -> bool {
    let p = p();
    let (x1, y1, z1) = a;
    let (x2, y2, z2) = b;
    let inf1 = z1 == UBig::ZERO;
    let inf2 = z2 == UBig::ZERO;
    if inf1 || inf2 {
        return inf1 == inf2;
    }
    let z1_2 = (&z1 * &z1) % &p;
    let z2_2 = (&z2 * &z2) % &p;
    let x_ok = (&x1 * &z2_2) % &p == (&x2 * &z1_2) % &p;
    let y_ok = (&y1 * &z2_2 * &z2) % &p == (&y2 * &z1_2 * &z1) % &p;
    x_ok && y_ok
}

#[test]
fn pm_curve_matches_montgomery_native() {
    // d·G must be the same point on both representations of the curve.
    for d in [1u64, 2, 3, 5, 1000, 0x0123456789abcdef] {
        let scalar = CompositeWord::<u64, 4>::from_le_words([d, 0, 0, 0]);
        let mont = coords(&(Secp256k1.g() * scalar));
        let pm = coords(&(Secp256k1PM.g() * scalar));
        assert!(jacobian_eq(mont, pm), "PM vs Montgomery mismatch for d={d}");
    }
    // a full-width scalar
    let scalar = CompositeWord::<u64, 4>::from_le_words([
        0x0123456789abcdef,
        0xfedcba9876543210,
        0x13579bdf02468ace,
        0x0f1e2d3c4b5a6978,
    ]);
    let mont = coords(&(Secp256k1.g() * scalar));
    let pm = coords(&(Secp256k1PM.g() * scalar));
    assert!(
        jacobian_eq(mont, pm),
        "PM vs Montgomery mismatch (full width)"
    );
}

/// Circuit: output 1 iff the PM fixed-base comb agrees with the native PM scalar multiplication.
struct PmFixedBaseEqNative {
    scalar: CompositeWord<u64, 4>,
}
impl Circuit for PmFixedBaseEqNative {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        use zkboo_ecc::montgomery::PointFrontendIO;
        let got = Secp256k1PM.g().mul_secret_scalar(fe.input(self.scalar));
        let want = fe.point_input(Secp256k1PM.g() * self.scalar);
        fe.output(got.eq(want).into());
    }
}

#[test]
fn pm_fixed_base_circuit() {
    for d in [
        CompositeWord::<u64, 4>::from_le_words([7, 0, 0, 0]),
        CompositeWord::<u64, 4>::from_le_words([
            0x0123456789abcdef,
            0xfedcba9876543210,
            0x13579bdf02468ace,
            0x0f1e2d3c4b5a6978,
        ]),
    ] {
        let outputs = exec::<_, WP, _>(&PmFixedBaseEqNative { scalar: d }, ExecOptions::new());
        let mut expected = Words::new();
        expected.as_vec_mut::<u8>().push(1);
        assert_eq!(outputs, expected, "PM fixed-base != native for {d:?}");
    }
}
