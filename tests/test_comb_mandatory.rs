// SPDX-License-Identifier: LGPL-3.0-or-later

//! Soundness coverage for the signed-digit fixed-base comb ([`Curve::mul_secret_scalar`]).
//!
//! The comb adds each window with the cheap mixed addition, except the top window, which uses the
//! complete addition because that is the only window where the accumulated partial sum can equal or
//! oppose the table point. The canonical witness is `d = 2^256 − n`: its recoding forces the top
//! digit to a multiple whose point equals the partial sum modulo `n`, so a mixed add there would
//! silently return the wrong point. This test pins `d = 2^256 − n` alongside the other boundary
//! scalars (0, n, n±k, single bits, dense patterns, per-window multiples) and a random sweep, for
//! both the Montgomery and the pseudo-Mersenne (production) field backends, checking the in-circuit
//! comb against the native reference with projective equality.

use zkboo::{
    backend::{Backend, Frontend},
    circuit::Circuit,
    executor::{OwnedFlexibleWordPool, exec},
    word::{CompositeWord, Words},
};
use zkboo_ecc::montgomery::{Curve, PointFrontendIO};
use zkboo_ecc::secp256k1::{Secp256k1, Secp256k1PM};
use zkboo::executor::ExecOptions;

type WP = OwnedFlexibleWordPool<usize>;

/// Circuit: output `1` iff `scalar · G` via the fixed-base comb equals the native reference point.
struct CombEqNative<C: Curve<u64, 4>> {
    curve: C,
    scalar: CompositeWord<u64, 4>,
}

impl<C: Curve<u64, 4>> Circuit for CombEqNative<C> {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        let got = self.curve.g().mul_secret_scalar(fe.input(self.scalar));
        let want = fe.point_input(self.curve.g() * self.scalar);
        fe.output(got.eq(want).into());
    }
}

fn check<C: Curve<u64, 4>>(curve: C, scalar: CompositeWord<u64, 4>) {
    let outputs = exec::<_, WP, _>(&CombEqNative { curve, scalar }, ExecOptions::new());
    let mut expected = Words::new();
    expected.as_vec_mut::<u8>().push(1);
    assert_eq!(outputs, expected, "comb wrong for scalar={scalar:?}");
}

/// A small canonical value `[k, 0, 0, 0]`.
fn w(k: u64) -> CompositeWord<u64, 4> {
    return CompositeWord::from_le_words([k, 0, 0, 0]);
}

/// splitmix64 — a deterministic, dependency-free source for the random sweep.
fn next(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    return z ^ (z >> 31);
}

/// The mandatory boundary scalars, shared by both curves (same order `n`, same generator).
fn mandatory_scalars<C: Curve<u64, 4>>(curve: C) -> Vec<CompositeWord<u64, 4>> {
    let n = curve.n();
    let two256_minus_n = CompositeWord::<u64, 4>::ZERO.wrapping_sub(n); // 2^256 − n
    let one = CompositeWord::<u64, 4>::ONE;
    let mut scalars = vec![
        // The dangerous scalar and its neighbours: pure mixed add MUST fail here.
        two256_minus_n,
        two256_minus_n.wrapping_add(one),
        two256_minus_n.wrapping_sub(one),
        two256_minus_n.wrapping_add(w(2)),
        two256_minus_n.wrapping_sub(w(2)),
        // Order-related edges (all map to O or ±small·G).
        CompositeWord::ZERO,
        one,
        w(2),
        n,
        n.wrapping_sub(one),
        n.wrapping_add(one),
        n.wrapping_sub(w(2)),
        n.wrapping_add(w(2)),
        // High bit and its neighbours.
        one << 255,
        (one << 255).wrapping_sub(one),
        (one << 255).wrapping_add(one),
        // Small even and odd.
        w(3),
        w(17),
        w(31),
        w(64),
        // Dense patterns.
        CompositeWord::MAX,
        CompositeWord::from_le_words([0xAAAA_AAAA_AAAA_AAAA; 4]),
        CompositeWord::from_le_words([0x5555_5555_5555_5555; 4]),
    ];
    // Single bits across word and window boundaries.
    for i in [0usize, 4, 5, 6, 63, 64, 127, 128, 250, 254, 255] {
        scalars.push(one << i);
    }
    // Per-window multiples j · 2^{5k}: partial-sum stress at several windows.
    for k in [0usize, 1, 10, 25, 49, 50, 51] {
        for j in [1u64, 2, 15, 16, 17, 31] {
            scalars.push((one << (5 * k)).wrapping_mul(w(j)));
        }
    }
    // Deterministic random sweep.
    let mut state = 0xC0FF_EE12_3456_789Au64;
    for _ in 0..64 {
        scalars.push(CompositeWord::from_le_words([
            next(&mut state),
            next(&mut state),
            next(&mut state),
            next(&mut state),
        ]));
    }
    return scalars;
}

#[test]
fn comb_mandatory_scalars_montgomery() {
    for scalar in mandatory_scalars(Secp256k1) {
        check(Secp256k1, scalar);
    }
}

#[test]
fn comb_mandatory_scalars_pseudo_mersenne() {
    for scalar in mandatory_scalars(Secp256k1PM) {
        check(Secp256k1PM, scalar);
    }
}
