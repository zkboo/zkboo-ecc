// SPDX-License-Identifier: LGPL-3.0-or-later

//! An end-to-end proof of a fixed-base scalar multiplication, for both combs.
//!
//! Everything else here checks circuits by executing them. That is not enough for the affine comb:
//! it rests on advice, which only exists in the prover, and on assertions, which only bite when a
//! verifier checks the word they accumulate into. The prover shares advice as it shares an input
//! and the verifier replays it as one — so nothing but a real proof exercises the seam between
//! them, over a statement with a hint and an assertion per window rather than one of each.
//!
//! Proving one is seconds in release and many minutes in debug, so the proving tests here are
//! `#[ignore]`d and meant to be run explicitly:
//!
//! ```text
//!   cargo test --release -p zkboo-ecc --test test_comb_proof -- --ignored
//! ```
//!
//! The cheap end of the same seam — a hinted inverse, proved and verified — runs by default in
//! `zkboo-modular`.

use zkboo::{
    backend::{Backend, Frontend, WordRef},
    circuit::{Assertions, Circuit},
    crypto::{HashPRG, Hasher},
    executor::{OwnedFlexibleWordPool, exec},
    prover::{prove, views::OwnedFlexibleWordTriplePool},
    verifier::{replay::OwnedFlexibleWordPairPool, verify},
    word::{CompositeWord, Words},
};
use zkboo_ecc::weierstrass::{
    Curve, HOST_COMB_WINDOW_BITS, PointFrontendIO, PrecomputedWindowTables, Squaring,
};
use zkboo_ecc::secp256k1::Secp256k1PM;
use zkboo_modular::montgomery::MontgomeryFrontendIO;
use zkboo::executor::ExecOptions;
use zkboo::prover::proof::ProofOptions;
use zkboo::verifier::VerifyOptions;
use zeroize::Zeroize;
use zkboo_profiling::profile;

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

type H = Blake3Hasher;
type PS = HashPRG<H>;
type PV = HashPRG<H>;
type S = <H as Hasher>::Digest;
type WP = OwnedFlexibleWordPool<usize>;
type WTP = OwnedFlexibleWordTriplePool<usize>;
type WPP = OwnedFlexibleWordPairPool<usize>;

const SEED_ENTROPY: &[u8] = b"comb proof seed entropy";
const BINDING: &[u8] = b"comb proof binding";
/// Enough repetitions to exercise the challenge over all three parties many times over, and few
/// enough to prove in seconds.
const NUM_ITERS: usize = 8;

const WINDOW_BITS: usize = 5;

/// `d·G` through the affine comb, output as its affine coordinates.
struct AffineComb {
    scalar: CompositeWord<u64, 4>,
    squaring: Squaring,
}

impl Circuit for AffineComb {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        Assertions::scope(fe, |asserts| {
            let mut tables = PrecomputedWindowTables::new(Secp256k1PM.g(), WINDOW_BITS);
            let (x, y) = Secp256k1PM.mul_secret_scalar_affine_with(
                fe,
                fe.input(self.scalar),
                Some(self.scalar),
                &mut tables,
                asserts,
                self.squaring,
            );
            fe.montgomery_output(x);
            fe.montgomery_output(y);
        });
    }
}

/// `d·G` through the affine comb, with the host mirror made an explicit choice: the prover holds
/// the scalar to mirror and the verifier does not.
struct AffineCombFor {
    scalar: CompositeWord<u64, 4>,
    scalar_value: Option<CompositeWord<u64, 4>>,
}

impl AffineCombFor {
    /// The prover's view: the scalar, and the scalar again to mirror.
    fn prover() -> Self {
        return Self {
            scalar: scalar(),
            scalar_value: Some(scalar()),
        };
    }

    /// The verifier's view: no input values and nothing to mirror.
    fn verifier() -> Self {
        return Self {
            scalar: CompositeWord::ZERO,
            scalar_value: None,
        };
    }
}

impl Circuit for AffineCombFor {
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

/// The same, through the Jacobian comb, so the hint-free path is covered too.
struct JacobianComb {
    scalar: CompositeWord<u64, 4>,
}

impl Circuit for JacobianComb {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        let mut tables = PrecomputedWindowTables::new(Secp256k1PM.g(), WINDOW_BITS);
        let point = Secp256k1PM.mul_secret_scalar(fe.input(self.scalar), &mut tables);
        fe.point_output_affine(point);
    }
}

fn prove_and_verify<C: Circuit + Sync>(circuit: &C, expected_output: &Words) -> bool {
    let proof = prove::<_, H, PS, PV, S, _, WTP, _>(circuit, NUM_ITERS, SEED_ENTROPY, BINDING, ProofOptions::new());
    return verify::<_, H, PV, S, WPP, _>(circuit, expected_output, &proof, BINDING, VerifyOptions::new())
        .expect("verification errored");
}

fn scalar() -> CompositeWord<u64, 4> {
    return CompositeWord::from_le_words([
        0x0123_4567_89ab_cdef,
        0xfedc_ba98_7654_3210,
        0x2468_ace0_1357_9bdf,
        0x0f1e_2d3c_4b5a_6978,
    ]);
}

#[test]
#[ignore = "proves and verifies a full secp256k1 statement; run explicitly in release mode"]
fn the_affine_comb_proves_and_verifies() {
    for squaring in [Squaring::Multiplication, Squaring::Dedicated] {
        let circuit = AffineComb {
            scalar: scalar(),
            squaring,
        };
        let expected_output = exec::<_, WP, _>(&circuit, ExecOptions::new());
        // The assertion word must be satisfied, or the statement below is about a failed proof.
        assert_eq!(expected_output.u8, vec![1u8], "assertions not satisfied");
        assert!(
            prove_and_verify(&circuit, &expected_output),
            "a proof of the affine comb did not verify ({squaring:?})"
        );
    }
}

#[test]
#[ignore = "proves and verifies a full secp256k1 statement; run explicitly in release mode"]
fn the_jacobian_comb_proves_and_verifies() {
    let circuit = JacobianComb { scalar: scalar() };
    let expected_output = exec::<_, WP, _>(&circuit, ExecOptions::new());
    assert!(
        prove_and_verify(&circuit, &expected_output),
        "a proof of the Jacobian comb did not verify"
    );
}

#[test]
fn the_affine_comb_and_the_jacobian_comb_agree() {
    let affine = exec::<_, WP, _>(&AffineComb {
        scalar: scalar(),
        squaring: Squaring::Multiplication,
    }, ExecOptions::new());
    let jacobian = exec::<_, WP, _>(&JacobianComb { scalar: scalar() }, ExecOptions::new());
    // The affine comb asserts, so it emits a flag the Jacobian one has no reason to; the
    // coordinates are what has to agree.
    assert_eq!(
        affine.u64, jacobian.u64,
        "the two combs disagree on the point"
    );
    assert_eq!(
        affine.u8,
        vec![1u8],
        "the affine comb's assertions did not hold"
    );
    assert!(
        jacobian.u8.is_empty(),
        "the Jacobian comb emits no assertion flag, having asserted nothing"
    );
}

#[test]
#[ignore = "proves and verifies a full secp256k1 statement; run explicitly in release mode"]
fn a_proof_of_a_violated_assertion_does_not_verify() {
    // `d ≡ 0 (mod n)` puts the product at infinity, which the affine comb asserts away. A prover
    // that tries anyway produces an assertion word of `0`, and no verifier expecting a satisfied
    // statement accepts it.
    let circuit = AffineComb {
        scalar: Secp256k1PM.n(),
        squaring: Squaring::Multiplication,
    };
    let violated = exec::<_, WP, _>(&circuit, ExecOptions::new());
    assert_eq!(violated.u8, vec![0u8], "the assertion was not violated");
    let mut satisfied = violated.clone();
    satisfied.as_vec_mut::<u8>()[0] = 1;
    assert!(
        !prove_and_verify(&circuit, &satisfied),
        "a proof of an infinite product verified"
    );
    // ... and it is the assertion word that rejects it: the same proof against its own output,
    // assertion word and all, is a perfectly good proof of a statement nobody wants.
    assert!(
        prove_and_verify(&circuit, &violated),
        "the proof is not otherwise well formed"
    );
}

/// The window count is what makes the assertions hold, so cover a width that is not the default.
#[test]
#[ignore = "proves and verifies a full secp256k1 statement; run explicitly in release mode"]
fn the_host_window_width_also_proves_and_verifies() {
    struct WideComb;
    impl Circuit for WideComb {
        fn exec<B: Backend>(&self, fe: &Frontend<B>) {
            Assertions::scope(fe, |asserts| {
                let mut tables =
                    PrecomputedWindowTables::new(Secp256k1PM.g(), HOST_COMB_WINDOW_BITS);
                let scalar_ref: WordRef<B, u64, 4> = fe.input(scalar());
                let (x, y) = Secp256k1PM.mul_secret_scalar_affine(
                    fe,
                    scalar_ref,
                    Some(scalar()),
                    &mut tables,
                    asserts,
                );
                fe.montgomery_output(x);
                fe.montgomery_output(y);
            });
        }
    }
    let expected_output = exec::<_, WP, _>(&WideComb, ExecOptions::new());
    assert!(
        prove_and_verify(&WideComb, &expected_output),
        "a proof at the host window width did not verify"
    );
}

#[test]
fn a_verifier_that_mirrors_no_scalar_runs_the_same_circuit() {
    // The host mirror is not a gate: whether the caller holds a scalar to mirror decides only
    // where a slope's value comes from, never what the circuit does with it.
    assert_eq!(
        format!("{:?}", profile(&AffineCombFor::prover())),
        format!("{:?}", profile(&AffineCombFor::verifier())),
        "mirroring a scalar changed the circuit"
    );
}

#[test]
#[ignore = "proves and verifies a full secp256k1 statement; run explicitly in release mode"]
fn a_verifier_that_mirrors_no_scalar_still_verifies() {
    let prover = AffineCombFor::prover();
    let expected_output = exec::<_, WP, _>(&prover, ExecOptions::new());
    assert_eq!(expected_output.u8, vec![1u8], "assertions not satisfied");
    let proof = prove::<_, H, PS, PV, S, _, WTP, _>(
        &prover,
        NUM_ITERS,
        SEED_ENTROPY,
        BINDING,
        ProofOptions::new(),
    );
    let is_valid = verify::<_, H, PV, S, WPP, _>(
        &AffineCombFor::verifier(),
        &expected_output,
        &proof,
        BINDING,
        VerifyOptions::new(),
    )
    .expect("verification errored");
    assert!(
        is_valid,
        "a verifier holding no scalar to mirror failed to verify an honest proof"
    );
}
