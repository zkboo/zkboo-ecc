// SPDX-License-Identifier: LGPL-3.0-or-later

//! The affine comb's circuit fingerprint, pinned.
//!
//! A fingerprint ingests every operation in the order the circuit issues it, so it moves whenever a
//! gate is added, removed or reordered. Two things are checked against it: that the comb's gates do
//! not drift, and that whether the caller supplies a scalar for the host mirror to follow makes no
//! difference to them — the mirror decides where a slope's value comes from and nothing else.

use zeroize::Zeroize;
use zkboo::{
    backend::{Backend, Frontend},
    circuit::{Assertions, Circuit},
    crypto::Hasher,
    word::CompositeWord,
};
use zkboo_circuit_hash::hash_circuit;
use zkboo_ecc::secp256k1::Secp256k1PM;
use zkboo_ecc::weierstrass::{Curve, PrecomputedWindowTables};
use zkboo_modular::montgomery::MontgomeryFrontendIO;

/// A [Hasher] backed by BLAKE3, producing 32-byte digests.
#[derive(Debug)]
struct Blake3Hasher {
    inner: blake3::Hasher,
}

impl Hasher for Blake3Hasher {
    type Digest = [u8; 32];
    const DIGEST_SIZE: usize = 32;

    fn new() -> Self {
        return Self {
            inner: blake3::Hasher::new(),
        };
    }

    fn update(&mut self, data: &[u8]) {
        self.inner.update(data);
    }

    fn finalize_into(&mut self, out: &mut Self::Digest) {
        let result = self.inner.finalize();
        out.copy_from_slice(result.as_bytes());
        self.inner.reset();
    }
}

impl Zeroize for Blake3Hasher {
    fn zeroize(&mut self) {
        self.inner.reset();
    }
}

const WINDOW_BITS: usize = 5;

/// BLAKE3 fingerprint of [`AffineComb`] at the default window width.
const PINNED_FINGERPRINT: &str =
    "0eeb08dd52dbd4df8f95410152b53b7c2bc940df2bf78b747a60be25ef1a20ae";

fn scalar() -> CompositeWord<u64, 4> {
    return CompositeWord::from_le_words([
        0x0123_4567_89ab_cdef,
        0xfedc_ba98_7654_3210,
        0x2468_ace0_1357_9bdf,
        0x0f1e_2d3c_4b5a_6978,
    ]);
}

struct AffineComb {
    scalar: CompositeWord<u64, 4>,
    scalar_value: Option<CompositeWord<u64, 4>>,
}

impl Circuit for AffineComb {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        Assertions::scope(fe, |asserts| {
            let mut tables = PrecomputedWindowTables::new(Secp256k1PM.g(), WINDOW_BITS);
            let (x, y) = Secp256k1PM.mul_secret_scalar_affine(
                fe,
                fe.input(self.scalar),
                self.scalar_value,
                &mut tables,
                asserts,
            );
            fe.montgomery_output(x);
            fe.montgomery_output(y);
        });
    }
}

fn hex(bytes: &[u8]) -> String {
    return bytes.iter().map(|b| format!("{b:02x}")).collect();
}

fn fingerprint(circuit: &AffineComb) -> String {
    return hex(&hash_circuit::<_, Blake3Hasher>(circuit));
}

#[test]
fn the_affine_comb_fingerprint_is_pinned() {
    let prover = AffineComb {
        scalar: scalar(),
        scalar_value: Some(scalar()),
    };
    assert_eq!(
        fingerprint(&prover),
        PINNED_FINGERPRINT,
        "the affine comb's gates changed"
    );
}

#[test]
fn mirroring_a_scalar_does_not_change_the_comb() {
    let prover = AffineComb {
        scalar: scalar(),
        scalar_value: Some(scalar()),
    };
    let verifier = AffineComb {
        scalar: CompositeWord::ZERO,
        scalar_value: None,
    };
    assert_eq!(
        fingerprint(&prover),
        fingerprint(&verifier),
        "supplying a scalar to mirror changed the circuit"
    );
}
