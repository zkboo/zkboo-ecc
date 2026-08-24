// SPDX-License-Identifier: LGPL-3.0-or-later

//! Correctness of the signed-digit fixed-base comb across window widths.
//!
//! [`Curve::mul_secret_scalar`] recodes the scalar one window at a time, carrying a residual that
//! the top window consumes whole. That residual is only guaranteed to fit the top window's `w − 1`
//! index bits when the windows cover at least one bit more than the scalar; when the window width
//! divides the scalar width exactly, they do not, and the residual's top bit must still be carried —
//! silently returning the wrong point for widths `w ∈ {2, 4, 8, 16}` on a 256-bit scalar. (A
//! one-bit window is rejected outright: it leaves the magnitude mux with no index bits.)
//!
//! [`test_comb_mandatory`](../test_comb_mandatory.rs) covers the boundary scalars at the default
//! width; this test covers every width, and pins the scalars that reach the top window's doubling
//! branch at the widths a host prover is likely to choose.

use zkboo::{
    backend::{Backend, Frontend},
    circuit::Circuit,
    executor::{OwnedFlexibleWordPool, exec},
    word::{CompositeWord, Words},
};
use zkboo_ecc::montgomery::{ComputedWindowTables, Curve, PointFrontendIO};
use zkboo_ecc::secp256k1::{Secp256k1, Secp256k1PM};

type WP = OwnedFlexibleWordPool<usize>;

/// Circuit: output `1` iff `scalar · G` via the comb at width `w` equals the native reference.
struct CombEqNative<C: Curve<u64, 4>> {
    curve: C,
    scalar: CompositeWord<u64, 4>,
    w: usize,
}

impl<C: Curve<u64, 4>> Circuit for CombEqNative<C> {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        let mut tables = ComputedWindowTables::new(self.curve.g(), self.w);
        let got = self
            .curve
            .mul_secret_scalar(fe.input(self.scalar), &mut tables);
        let want = fe.point_input(self.curve.g() * self.scalar);
        fe.output(got.eq(want).into());
    }
}

fn check<C: Curve<u64, 4>>(curve: C, scalar: CompositeWord<u64, 4>, w: usize) {
    let outputs = exec::<_, WP>(&CombEqNative { curve, scalar, w });
    let mut expected = Words::new();
    expected.as_vec_mut::<u8>().push(1);
    assert_eq!(outputs, expected, "comb wrong for w={w}, scalar={scalar:?}");
}

/// A small canonical value `[k, 0, 0, 0]`.
fn w_(k: u64) -> CompositeWord<u64, 4> {
    return CompositeWord::from_le_words([k, 0, 0, 0]);
}

/// Boundary scalars that stress the top window's residual: the widths exercised here all
/// failed on at least one of these.
fn probe_scalars<C: Curve<u64, 4>>(curve: C) -> Vec<CompositeWord<u64, 4>> {
    let n = curve.n();
    let one = CompositeWord::<u64, 4>::ONE;
    let zero = CompositeWord::<u64, 4>::ZERO;
    return vec![
        zero,
        one,
        w_(2),
        zero.wrapping_sub(n),          // 2^256 − n, the doubling witness at w = 5
        zero.wrapping_sub(one),        // 2^256 − 1
        zero.wrapping_sub(w_(2)),      // 2^256 − 2
        n,
        n.wrapping_sub(one),
        n.wrapping_add(one),
        one << 255,
        (one << 255).wrapping_sub(one),
        CompositeWord::MAX,
        CompositeWord::from_le_words([0xAAAA_AAAA_AAAA_AAAA; 4]),
        CompositeWord::from_le_words([0x5555_5555_5555_5555; 4]),
    ];
}

/// Every window width must agree with the native reference, in particular the widths that divide
/// the 256-bit scalar width (`2, 4, 8, 16`), which have no spare bit for the top residual.
#[test]
fn every_window_width_matches_the_native_reference() {
    for w in 2..=16usize {
        for scalar in probe_scalars(Secp256k1PM) {
            check(Secp256k1PM, scalar, w);
        }
    }
}

/// The same sweep on the Montgomery field backend, at the widths that divide the scalar width plus
/// a couple of neighbours — the recoding is field-independent, so this is a cheap cross-check.
#[test]
fn dividing_widths_match_on_the_montgomery_backend() {
    for w in [2usize, 3, 4, 5, 8, 16] {
        for scalar in probe_scalars(Secp256k1) {
            check(Secp256k1, scalar, w);
        }
    }
}

/// Scalars that drive the top window into its doubling case (`partial sum ≡ table point mod n`),
/// where the complete addition's doubling arm is the only correct answer.
///
/// The witness is width-specific: `2^256 − n` reaches the doubling arm at `w = 5` (the default,
/// pinned in `test_comb_mandatory`) but not at `w = 9` or `w = 11`, which a host prover with room
/// for larger tables would pick. Without these the arm goes untested at those widths.
#[test]
fn top_window_doubling_witnesses() {
    // w = 5: 2^256 − n, the witness pinned in `test_comb_mandatory`.
    check(
        Secp256k1PM,
        CompositeWord::<u64, 4>::ZERO.wrapping_sub(Secp256k1PM.n()),
        5,
    );
    // w = 9: 0xe000…014551231950b75fc4402da1732fc9bebf
    check(
        Secp256k1PM,
        CompositeWord::from_be_words([
            0xe000_0000_0000_0000,
            0x0000_0000_0000_0001,
            0x4551_2319_50b7_5fc4,
            0x402d_a173_2fc9_bebf,
        ]),
        9,
    );
    // w = 11: 0xc000…014551231950b75fc4402da1732fc9bebf
    check(
        Secp256k1PM,
        CompositeWord::from_be_words([
            0xc000_0000_0000_0000,
            0x0000_0000_0000_0001,
            0x4551_2319_50b7_5fc4,
            0x402d_a173_2fc9_bebf,
        ]),
        11,
    );
}
