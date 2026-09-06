// SPDX-License-Identifier: LGPL-3.0-or-later

//! Converting a point to affine coordinates by assertion rather than by computation.
//!
//! A modular inversion in circuit costs a full run of divsteps; checking a pair of affine
//! coordinates costs two field multiplications. So the coordinates arrive as advice and the circuit
//! asserts what defines them — that they scale back to the projective coordinates it computed.

use zkboo::{
    backend::{Backend, Frontend},
    circuit::{Assertions, Circuit},
    executor::{ExecOptions, OwnedFlexibleWordPool, exec},
    word::{CompositeWord, Words},
};
use zkboo_ecc::secp256k1::Secp256k1PM;
use zkboo_ecc::weierstrass::{Curve, PrecomputedWindowTables};
use zkboo_modular::montgomery::{Montgomery, MontgomeryFrontendIO};
use zkboo_profiling::profile;

type WP = OwnedFlexibleWordPool<usize>;
type Word4 = CompositeWord<u64, 4>;

const WINDOW_BITS: usize = 5;

fn scalar() -> Word4 {
    return CompositeWord::from_le_words([9, 0, 0, 0]);
}

/// What the circuit does with the Jacobian point the comb leaves it.
#[derive(Clone, Copy)]
enum Convert {
    /// Output the projective coordinates untouched, to price a conversion by difference.
    None_,
    /// Compute the affine coordinates.
    Computed,
    /// Assert the affine coordinates against the given advice.
    Advised([Montgomery<u64, 4>; 2]),
}

struct Statement {
    convert: Convert,
}

impl Circuit for Statement {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        Assertions::scope(fe, |asserts| {
            let mut tables = PrecomputedWindowTables::new(Secp256k1PM.g(), WINDOW_BITS);
            let p = Secp256k1PM.mul_secret_scalar(fe.input(scalar()), &mut tables);
            let out = match self.convert {
                Convert::None_ => p,
                Convert::Computed => p.to_affine(),
                Convert::Advised(advice) => p.to_affine_advised(fe, Some(advice), asserts),
            };
            // The stored representation, which is what the assertion compares against and what the
            // advised form takes back. `montgomery_output` would emit the canonical residue, which
            // is a different word for a Montgomery modulus and the same one for a pseudo-Mersenne
            // modulus — so getting this wrong is invisible on this curve and fatal on Ed25519.
            let [x, y, _] = out.into_coords();
            fe.montgomery_output_inner(x);
            fe.montgomery_output_inner(y);
        });
    }
}

fn run(convert: Convert) -> Words {
    return exec::<_, WP, _>(&Statement { convert }, ExecOptions::new());
}

fn cost(convert: Convert) -> usize {
    return profile(&Statement { convert }).and_msg_size().sum();
}

/// The advice a correct prover supplies, taken from the computed conversion.
fn honest_advice() -> [Montgomery<u64, 4>; 2] {
    let limbs = run(Convert::Computed).as_vec::<u64>().to_vec();
    assert_eq!(limbs.len(), 8, "two coordinates of four limbs each");
    return [
        Montgomery::from_raw(CompositeWord::from_le_words([
            limbs[0], limbs[1], limbs[2], limbs[3],
        ])),
        Montgomery::from_raw(CompositeWord::from_le_words([
            limbs[4], limbs[5], limbs[6], limbs[7],
        ])),
    ];
}

#[test]
fn asserted_coordinates_agree_with_computed_ones() {
    let computed = run(Convert::Computed);
    let asserted = run(Convert::Advised(honest_advice()));
    assert_eq!(
        computed.u64, asserted.u64,
        "the asserted conversion disagrees with the computed one"
    );
    assert_eq!(asserted.u8, vec![1u8], "honest advice failed its assertion");
}

#[test]
fn wrong_coordinates_violate_the_assertion() {
    let [x, y] = honest_advice();
    let flip = |m: Montgomery<u64, 4>| Montgomery::from_raw(m.into_raw() ^ Word4::ONE);
    for advice in [[flip(x), y], [x, flip(y)]] {
        assert_eq!(
            run(Convert::Advised(advice)).u8,
            vec![0u8],
            "a coordinate off by one bit passed the assertion"
        );
    }
}

#[test]
fn asserting_the_conversion_is_far_cheaper_than_computing_it() {
    let baseline = cost(Convert::None_);
    let computed = cost(Convert::Computed) - baseline;
    let asserted = cost(Convert::Advised(honest_advice())) - baseline;
    assert!(
        computed / asserted >= 8,
        "the asserted conversion is not eight times cheaper: {asserted} against {computed}"
    );
}
