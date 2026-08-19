// SPDX-License-Identifier: LGPL-3.0-or-later

//! Data-obliviousness and gate-count pin for the signed-digit fixed-base comb.

use zkboo::{
    backend::{Backend, Frontend},
    circuit::Circuit,
    word::CompositeWord,
};
use zkboo_ecc::montgomery::Curve;
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
