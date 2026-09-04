// SPDX-License-Identifier: LGPL-3.0-or-later

//! [`PrecomputedWindowTables`] against the on-demand [`ComputedWindowTables`].
//!
//! The two sources must be interchangeable: same window count, same points, same comb result. They
//! differ only in when the native arithmetic runs — once up front against once per window request —
//! and in whether windows may be revisited.

use zkboo::{
    backend::{Backend, Frontend},
    circuit::Circuit,
    executor::{OwnedFlexibleWordPool, exec},
    word::{CompositeWord, Words},
};
use zkboo_ecc::montgomery::{
    ComputedWindowTables, Curve, PointFrontendIO, PrecomputedWindowTables, WindowTables,
    comb_window_count,
};
use zkboo_ecc::secp256k1::Secp256k1PM;
use zkboo::executor::ExecOptions;

type WP = OwnedFlexibleWordPool<usize>;

/// Widths worth covering: the smallest legal one, the device default, the host default, and two
/// that divide the scalar width (where the extra window lives).
const WIDTHS: [usize; 6] = [2, 4, 5, 8, 9, 11];

#[test]
fn precomputed_windows_match_the_on_demand_source() {
    for w in WIDTHS {
        let mut computed = ComputedWindowTables::new(Secp256k1PM.g(), w);
        let mut precomputed = PrecomputedWindowTables::new(Secp256k1PM.g(), w);
        let num_windows = comb_window_count(256, w);
        assert_eq!(
            precomputed.num_windows(),
            num_windows,
            "window count, w={w}"
        );
        assert_eq!(
            precomputed.len(),
            num_windows << (w - 1),
            "table size, w={w}"
        );
        for k in 0..num_windows {
            assert_eq!(
                computed.window(k),
                precomputed.window(k),
                "window {k} differs, w={w}"
            );
        }
    }
}

#[test]
fn windows_are_randomly_accessible() {
    let w = 5;
    let num_windows = comb_window_count(256, w);
    let mut precomputed = PrecomputedWindowTables::new(Secp256k1PM.g(), w);
    let forward: Vec<_> = (0..num_windows)
        .map(|k| precomputed.window(k).to_vec())
        .collect();
    // Backwards, then the first window again: an on-demand source rejects both.
    for k in (0..num_windows).rev() {
        assert_eq!(precomputed.window(k), forward[k], "window {k} on revisit");
    }
    assert_eq!(precomputed.window(0), forward[0], "window 0 on revisit");
}

/// Circuit: output `1` iff `scalar · G` via the comb at width `w` equals the native reference.
struct CombEqNative {
    scalar: CompositeWord<u64, 4>,
    w: usize,
}

impl Circuit for CombEqNative {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        let mut tables = PrecomputedWindowTables::new(Secp256k1PM.g(), self.w);
        let got = Secp256k1PM.mul_secret_scalar(fe.input(self.scalar), &mut tables);
        let want = fe.point_input(Secp256k1PM.g() * self.scalar);
        fe.output(got.eq(want).into());
    }
}

#[test]
fn the_comb_over_precomputed_tables_matches_the_native_reference() {
    let n = Secp256k1PM.n();
    let zero = CompositeWord::<u64, 4>::ZERO;
    let scalars = [
        CompositeWord::<u64, 4>::ONE,
        zero.wrapping_sub(n), // 2^256 − n, the top window's doubling case at w = 5
        CompositeWord::MAX,
        n.wrapping_sub(CompositeWord::ONE),
    ];
    let mut expected = Words::new();
    expected.as_vec_mut::<u8>().push(1);
    for scalar in scalars {
        for w in [5, 8, 9] {
            let outputs = exec::<_, WP, _>(&CombEqNative { scalar, w }, ExecOptions::new());
            assert_eq!(outputs, expected, "comb wrong for w={w}, scalar={scalar:?}");
        }
    }
}
