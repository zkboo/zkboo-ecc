// SPDX-License-Identifier: LGPL-3.0-or-later

//! Validates the data-oblivious fixed-base scalar multiplication
//! [`CurvePoint::mul_secret_scalar`] against the native (cleartext) scalar multiplication, for the
//! secp256k1 generator and a spread of secret scalars.
//!
//! The check is done with the in-circuit projective equality `CurvePointRef::eq` (no modular
//! inversion / affine conversion), keeping the interpreter cost to the windowed additions alone.

use zkboo::{
    backend::{Backend, Frontend},
    circuit::Circuit,
    executor::{OwnedFlexibleWordPool, exec},
    word::{CompositeWord, Words},
};
use zkboo_ecc::montgomery::{Curve, PointFrontendIO};
use zkboo_ecc::secp256k1::Secp256k1;

type WP = OwnedFlexibleWordPool<usize>;

/// Circuit: output `1` iff `scalar · G` via the fixed-base comb equals the native reference point.
struct FixedBaseEqNative {
    scalar: CompositeWord<u64, 4>,
}

impl Circuit for FixedBaseEqNative {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        let got = Secp256k1.g().mul_secret_scalar(fe.input(self.scalar));
        // Native reference, allocated into the circuit as a (Jacobian) point.
        let want = fe.point_input(Secp256k1.g() * self.scalar);
        fe.output(got.eq(want).into());
    }
}

fn check(scalar: CompositeWord<u64, 4>) {
    let outputs = exec::<_, WP>(&FixedBaseEqNative { scalar });
    let mut expected = Words::new();
    expected.as_vec_mut::<u8>().push(1); // true
    assert_eq!(
        outputs, expected,
        "fixed-base mul wrong for scalar={scalar:?}"
    );
}

#[test]
fn fixed_base_small_scalars() {
    check(CompositeWord::from_le_words([1, 0, 0, 0]));
    check(CompositeWord::from_le_words([2, 0, 0, 0]));
    check(CompositeWord::from_le_words([17, 0, 0, 0]));
    check(CompositeWord::from_le_words([64, 0, 0, 0])); // window boundary at w=6
}

#[test]
fn fixed_base_full_width_scalars() {
    check(CompositeWord::from_le_words([
        0x0123456789abcdef,
        0xfedcba9876543210,
        0x13579bdf02468ace,
        0x0f1e2d3c4b5a6978,
    ]));
    check(CompositeWord::from_le_words([
        0xffffffffffffffff,
        0x0000000000000000,
        0xffffffffffffffff,
        0x0000000000000001,
    ]));
}
