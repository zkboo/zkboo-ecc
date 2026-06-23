// SPDX-License-Identifier: LGPL-3.0-or-later

//! Gate-count regression benchmark for the secp256k1 field and curve operations.
//!
//! Reports the number of nonlinear (AND + carry) machine-word messages per operation — the
//! quantity that drives ZKBoo proof size and prover/verifier cost — using the gate-counting
//! `zkboo-profiling` backend, which runs without evaluating the circuit (so even a full
//! secret-scalar multiplication profiles instantly).
//!
//! Run with the local zkboo / zkboo-modular working trees (mirrors the proofofseed workspace):
//!
//! ```text
//! cargo run --release --example profile_secp256k1 \
//!   --config 'patch.crates-io.zkboo.path="../zkboo"' \
//!   --config 'patch.crates-io.zkboo-modular.path="../zkboo-modular"'
//! ```

use zkboo::backend::{Backend, Frontend};
use zkboo::circuit::Circuit;
use zkboo::word::CompositeWord;
use zkboo_ecc::montgomery::{Curve, PointFrontendIO};
use zkboo_ecc::secp256k1::{Secp256k1, Secp256k1Field, Secp256k1PM};
use zkboo_modular::montgomery::MontgomeryWordRef;
use zkboo_profiling::profile;

type MW<B> = MontgomeryWordRef<B, u64, 4, Secp256k1Field>;

fn a_word<B: Backend>(fe: &Frontend<B>) -> zkboo::backend::WordRef<B, u64, 4> {
    fe.input(CompositeWord::<u64, 4>::from_le_words([3, 5, 7, 9]))
}
fn mw<B: Backend>(fe: &Frontend<B>) -> MW<B> {
    MontgomeryWordRef::from_inner(a_word(fe), Secp256k1Field)
}

struct FieldMul;
impl Circuit for FieldMul {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        fe.output((mw(fe) * mw(fe)).into_inner());
    }
}
struct FieldInv;
impl Circuit for FieldInv {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        fe.output(mw(fe).inv().into_inner());
    }
}
struct PointDouble;
impl Circuit for PointDouble {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        fe.point_output_jacobian(fe.point_input(Secp256k1.g()).double());
    }
}
struct PointAdd;
impl Circuit for PointAdd {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        let g = Secp256k1.g();
        let p = fe.point_input(g);
        let q = fe.point_input(g.double());
        fe.point_output_jacobian(p + q);
    }
}
/// The elephant: d·G for a secret scalar d, output in affine form (includes one inversion).
/// Generic double-and-add ladder (base treated as a circuit variable).
struct ScalarMulLadder;
impl Circuit for ScalarMulLadder {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        let p = fe.point_input(Secp256k1.g());
        let d = a_word(fe);
        fe.point_output_affine(p * d);
    }
}
/// Same elephant via the fixed-base comb (G is a build-time constant), Montgomery field.
struct ScalarMulFixedBase;
impl Circuit for ScalarMulFixedBase {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        let d = a_word(fe);
        fe.point_output_affine(Secp256k1.g().mul_secret_scalar(d));
    }
}
/// Fixed-base comb over the pseudo-Mersenne field (same curve, cheaper reduction).
struct ScalarMulFixedBasePM;
impl Circuit for ScalarMulFixedBasePM {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        let d = a_word(fe);
        fe.point_output_affine(Secp256k1PM.g().mul_secret_scalar(d));
    }
}

// Production soundness: 219 responses = 64-bit post-quantum / 128-bit classical (zkboo n_eps(64)).
const NUM_ITERS: usize = 219;

fn report<C: Circuit>(label: &str, c: &C) {
    let data = profile(c);
    let nl = data.and_msg_size().sum();
    // Full proof size in bytes at the production repetition count, with 32-byte Keccak digests/seeds.
    let proof_mib = data.proof_size::<[u8; 32], [u8; 32]>(NUM_ITERS) as f64 / (1024.0 * 1024.0);
    println!("{label:<34} nl_and_msgs = {nl:>10}   proof @219 = {proof_mib:>9.1} MiB");
}

fn main() {
    println!("=== secp256k1 nonlinear gate counts (zkboo-profiling) ===");
    report("field mul", &FieldMul);
    report("field inv (safegcd)", &FieldInv);
    report("point double", &PointDouble);
    report("point add", &PointAdd);
    report("scalar mul d·G (ladder)", &ScalarMulLadder);
    report("scalar mul d·G (fixed-base, Mont)", &ScalarMulFixedBase);
    report("scalar mul d·G (fixed-base, PM)", &ScalarMulFixedBasePM);
}
