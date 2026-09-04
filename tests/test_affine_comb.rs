// SPDX-License-Identifier: LGPL-3.0-or-later

//! The affine comb, against the Jacobian one it is meant to replace.
//!
//! [`Curve::mul_secret_scalar_affine`] accumulates in affine coordinates, taking each addition's
//! slope as advice and asserting it. Three things need checking: that it agrees with the native
//! reference wherever it is defined; that the scalars where it is *not* defined — the multiples of
//! the group order, whose product is the point at infinity — fail their assertions rather than
//! producing a wrong answer; and that the last window's doubling branch is actually exercised.

use zkboo::{
    backend::{Backend, Frontend},
    circuit::{Assertions, Circuit},
    executor::{OwnedFlexibleWordPool, exec},
    word::{CompositeWord, Words},
};
use zkboo_ecc::weierstrass::{AffineCombAdvice, Curve, PrecomputedWindowTables, Squaring};
use zkboo_ecc::secp256k1::{Secp256k1, Secp256k1PM};
use zkboo::executor::ExecOptions;

type WP = OwnedFlexibleWordPool<usize>;
type Word4 = CompositeWord<u64, 4>;

/// Outputs `1` iff the affine comb's result equals the native reference, at window width `w`.
struct AffineCombEqNative<C: Curve<u64, 4>> {
    curve: C,
    scalar: Word4,
    w: usize,
    squaring: Squaring,
}

impl<C: Curve<u64, 4>> Circuit for AffineCombEqNative<C> {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        let mut asserts = Assertions::new();
        let mut tables = PrecomputedWindowTables::new(self.curve.g(), self.w);
        let advice = AffineCombAdvice::compute(self.curve, self.scalar, &mut tables);
        let (x, y) = self.curve.mul_secret_scalar_affine_with(
            fe,
            fe.input(self.scalar),
            &mut tables,
            &advice,
            &mut asserts,
            self.squaring,
        );
        // Compare against the native reference in its own (Jacobian) coordinates, by cross
        // multiplication: `x·Z² == X` and `y·Z³ == Y`. The scalars tested here all have a finite
        // product, so `Z` is nonzero and the comparison is exact.
        let [want_x, want_y, want_z] = (self.curve.g() * self.scalar).coords();
        let want_z2 = want_z * want_z;
        let want_z3 = want_z2 * want_z;
        let matches = (x * want_z2).eq_const(want_x) & (y * want_z3).eq_const(want_y);
        fe.output(matches.into());
        asserts.output(fe);
    }
}

/// Runs the affine comb and outputs nothing, so the whole output is the assertion word.
struct AffineCombOnly<C: Curve<u64, 4>> {
    curve: C,
    scalar: Word4,
    w: usize,
}

impl<C: Curve<u64, 4>> Circuit for AffineCombOnly<C> {
    fn exec<B: Backend>(&self, fe: &Frontend<B>) {
        let mut asserts = Assertions::new();
        let mut tables = PrecomputedWindowTables::new(self.curve.g(), self.w);
        let advice = AffineCombAdvice::compute(self.curve, self.scalar, &mut tables);
        let _ = self.curve.mul_secret_scalar_affine(
            fe,
            fe.input(self.scalar),
            &mut tables,
            &advice,
            &mut asserts,
        );
        asserts.output(fe);
    }
}

fn assertion_word(words: &Words) -> u8 {
    return *words
        .u8
        .last()
        .expect("the circuit outputs its assertion flag");
}

fn check<C: Curve<u64, 4>>(curve: C, scalar: Word4, w: usize) {
    check_with(curve, scalar, w, Squaring::Multiplication);
}

fn check_with<C: Curve<u64, 4>>(curve: C, scalar: Word4, w: usize, squaring: Squaring) {
    let out = exec::<_, WP, _>(&AffineCombEqNative {
        curve,
        scalar,
        w,
        squaring,
    }, ExecOptions::new());
    let mut expected = Words::new();
    // The comparison's `1`, then the assertion word — which must also be `1`, or the slopes the
    // prover supplied were not the slopes the circuit asked for.
    expected.as_vec_mut::<u8>().extend([1u8, 1u8]);
    assert_eq!(
        out, expected,
        "affine comb wrong for w={w}, scalar={scalar:?}"
    );
}

/// Scalars that stress the recoding's residual, all of them with a defined affine product.
fn probe_scalars<C: Curve<u64, 4>>(curve: C) -> Vec<Word4> {
    let n = curve.n();
    let one = Word4::ONE;
    let zero = Word4::ZERO;
    let two = CompositeWord::from_le_words([2, 0, 0, 0]);
    return vec![
        one,
        two,
        zero.wrapping_sub(n), // 2^256 − n, the top window's doubling case at w = 5
        zero.wrapping_sub(one), // 2^256 − 1
        zero.wrapping_sub(two), // 2^256 − 2
        n.wrapping_sub(one),
        n.wrapping_add(one),
        one << 255,
        (one << 255).wrapping_sub(one),
        CompositeWord::MAX,
        CompositeWord::from_le_words([0xAAAA_AAAA_AAAA_AAAA; 4]),
        CompositeWord::from_le_words([0x5555_5555_5555_5555; 4]),
    ];
}

#[test]
fn a_window_width_dividing_the_scalar_width_is_rejected() {
    // At such a width the recoding's windows reach exactly as far as the scalar, and a partial sum
    // can then be a multiple of the group order — the point at infinity, which an affine
    // accumulator cannot hold. `2^256 − n` at `w = 2` is such a case.
    let hook = std::panic::take_hook();
    std::panic::set_hook(std::boxed::Box::new(|_| {}));
    for w in [2usize, 4, 8, 16] {
        let result = std::panic::catch_unwind(|| {
            exec::<_, WP, _>(&AffineCombOnly {
                curve: Secp256k1PM,
                scalar: Word4::ONE,
                w,
            }, ExecOptions::new())
        });
        assert!(
            result.is_err(),
            "w={w} divides the scalar width but was accepted"
        );
    }
    std::panic::set_hook(hook);
}

#[test]
fn the_affine_comb_matches_the_native_reference() {
    for w in [3usize, 5, 6, 7, 9, 11] {
        for scalar in probe_scalars(Secp256k1PM) {
            check(Secp256k1PM, scalar, w);
        }
    }
}

#[test]
fn the_affine_comb_matches_on_the_montgomery_backend() {
    for scalar in probe_scalars(Secp256k1) {
        check(Secp256k1, scalar, 5);
    }
}

#[test]
fn a_scalar_whose_product_is_infinity_fails_its_assertions() {
    // `0` and `n` are exactly the scalars with `d·G = O`, and the affine accumulator cannot
    // represent infinity. The last window's cancellation assertion catches both: the result is not
    // wrong, it is unprovable.
    for scalar in [Word4::ZERO, Secp256k1PM.n()] {
        for w in [5usize, 9] {
            let out = exec::<_, WP, _>(&AffineCombOnly {
                curve: Secp256k1PM,
                scalar,
                w,
            }, ExecOptions::new());
            assert_eq!(
                assertion_word(&out),
                0,
                "an infinite product was accepted for w={w}, scalar={scalar:?}"
            );
        }
    }
}

#[test]
fn the_doubling_branch_of_the_last_window_is_covered() {
    // The last window doubles when the accumulated partial sum equals the table point it is added
    // to, which is a property of the width as well as the scalar: `2^256 − n` reaches it at `w = 5`
    // but at neither of the others, so each width needs its own witness. These are the same ones
    // `test_comb_window_widths` pins for the Jacobian comb.
    let witnesses: [(usize, Word4); 3] = [
        (5, Word4::ZERO.wrapping_sub(Secp256k1PM.n())),
        (
            9,
            CompositeWord::from_be_words([
                0xe000000000000000,
                0x0000000000000000,
                0x0000000000000001,
                0x4551231950b75fc4,
            ]),
        ),
        (
            11,
            CompositeWord::from_be_words([
                0xc000000000000000,
                0x0000000000000000,
                0x0000000000000001,
                0x4551231950b75fc4,
            ]),
        ),
    ];
    for (w, scalar) in witnesses {
        check(Secp256k1PM, scalar, w);
    }
}

#[test]
fn the_dedicated_squarer_gives_the_same_point() {
    // The squarer is a bit-level rearrangement of the multiplication, so choosing it must change
    // the gate count and nothing else.
    for scalar in probe_scalars(Secp256k1PM) {
        check_with(Secp256k1PM, scalar, 5, Squaring::Dedicated);
    }
}
