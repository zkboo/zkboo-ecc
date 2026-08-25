// SPDX-License-Identifier: LGPL-3.0-or-later

//! Data-obliviousness and gate-count pin for the signed-digit fixed-base comb.

use zkboo::{
    backend::{Backend, Frontend},
    circuit::Circuit,
    word::CompositeWord,
};
use zkboo_ecc::montgomery::{Curve, PrecomputedWindowTables};
use zkboo_ecc::secp256k1::Secp256k1PM;
use zkboo_profiling::profile;

struct Comb {
    scalar: CompositeWord<u64, 4>,
}

impl Circuit for Comb {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        let _ = Secp256k1PM.g().mul_secret_scalar(fe.input(self.scalar));
    }
}

#[test]
fn comb_is_data_oblivious_and_pinned() {
    let n = Secp256k1PM.n();
    let scalars = [
        CompositeWord::<u64, 4>::ONE,
        CompositeWord::<u64, 4>::ZERO.wrapping_sub(n), // 2^256 − n (the top-window doubling case)
        CompositeWord::<u64, 4>::MAX,
        CompositeWord::from_le_words([0xAAAA_AAAA_AAAA_AAAA; 4]),
    ];
    let counts: Vec<usize> = scalars
        .iter()
        .map(|&scalar| profile(&Comb { scalar }).and_msg_size().sum())
        .collect();
    // Data-oblivious: the AND-message count must not depend on the secret scalar.
    for c in &counts {
        assert_eq!(
            *c, counts[0],
            "comb gate count depends on the scalar (not data-oblivious): {counts:?}"
        );
    }
    // Regression pin: the signed-digit comb halves the AND messages of the previous
    // full-add-per-window comb (measured 2_742_474 → 1_337_465, a 2.05× reduction). A large upward
    // move means the mixed additions regressed; a large drop means the top-window complete addition
    // was accidentally replaced by a mixed one.
    assert_eq!(
        counts[0], COMB_AND_MSG_SIZE,
        "comb AND-message count changed"
    );
}

const COMB_AND_MSG_SIZE: usize = 1_337_465;

/// The same comb at an explicit window width, over a RAM-resident table.
struct CombAtWidth {
    scalar: CompositeWord<u64, 4>,
    w: usize,
}

impl Circuit for CombAtWidth {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        let mut tables = PrecomputedWindowTables::new(Secp256k1PM.g(), self.w);
        let _ = Secp256k1PM.mul_secret_scalar(fe.input(self.scalar), &mut tables);
    }
}

#[test]
fn per_width_gate_counts_are_pinned() {
    // Widening the window trades one mixed addition (25,594 nl) for a wider mux (`2^(w+1) + 16` nl
    // per window). The pins below are the whole curve of that trade over the widths a prover would
    // choose: the device default, the host default, and the flat optimum past which the mux starts
    // to cost more than the addition it saves.
    //
    //   Total(w) = (K − 2)·25,594 + 53,594 + K·(2^(w+1) + 16) + 11,   K = comb_window_count(256, w)
    //
    // reproduces every row exactly (the trailing 11 is the parity fix). The table source does not
    // enter the circuit, so `w = 5` must agree with `COMB_AND_MSG_SIZE` above to the gate.
    let pins = [(5usize, 1_337_465usize), (9, 774_803), (11, 715_361)];
    for (w, expected) in pins {
        let counts = profile(&CombAtWidth {
            scalar: CompositeWord::<u64, 4>::MAX,
            w,
        })
        .and_msg_size()
        .sum();
        assert_eq!(counts, expected, "comb AND-message count changed at w={w}");
    }
    assert_eq!(
        pins[0].1, COMB_AND_MSG_SIZE,
        "the RAM-resident table source changed the circuit at the default width"
    );
}
