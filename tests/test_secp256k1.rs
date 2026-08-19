// SPDX-License-Identifier: LGPL-3.0-or-later

use zkboo::{
    backend::{Backend, Frontend},
    circuit::Circuit,
    executor::{OwnedFlexibleWordPool, exec},
    word::CompositeWord,
};
use zkboo_ecc::montgomery::{Curve, CurvePoint, PointFrontendIO};
use zkboo_modular::montgomery::{MontgomeryMod, MontgomeryWord};

/// Modulus for the secp256k1 curve, implemented using 4x u64 limbs.
/// See https://std.neuromancer.sk/secg/secp256k1
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SECP256K1Mod;

impl MontgomeryMod<u64, 4> for SECP256K1Mod {
    #[inline]
    fn n(&self) -> CompositeWord<u64, 4> {
        return CompositeWord::from_be_words([
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xfffffffefffffc2f,
        ]);
    }

    #[inline]
    fn inv_exp(&self) -> Option<CompositeWord<u64, 4>> {
        return Some(CompositeWord::from_be_words([
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xfffffffefffffc2d,
        ]));
    }

    #[inline]
    fn rr_mod_n(&self) -> CompositeWord<u64, 4> {
        return CompositeWord::from_be_words([
            0x0000000000000000,
            0x0000000000000000,
            0x0000000000000001,
            0x000007a2000e90a1,
        ]);
    }

    #[inline]
    fn n_neg_inv(&self) -> CompositeWord<u64, 4> {
        return CompositeWord::from_be_words([
            0xc9bd190515538399,
            0x9c46c2c295f2b761,
            0xbcb223fedc24a059,
            0xd838091dd2253531,
        ]);
    }
}

/// The secp256k1 curve, implemented using 4x u64 limbs.
/// See https://std.neuromancer.sk/secg/secp256k1
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SECP256K1;

impl Curve<u64, 4> for SECP256K1 {
    type P = SECP256K1Mod;

    fn p(&self) -> Self::P {
        return SECP256K1Mod;
    }

    fn a(&self) -> MontgomeryWord<u64, 4, Self::P> {
        return MontgomeryWord::new(
            CompositeWord::from_be_words([
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ]),
            SECP256K1Mod,
        );
    }

    fn b(&self) -> MontgomeryWord<u64, 4, Self::P> {
        return MontgomeryWord::new(
            CompositeWord::from_be_words([
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000007,
            ]),
            SECP256K1Mod,
        );
    }

    fn g(&self) -> CurvePoint<u64, 4, Self> {
        let x = MontgomeryWord::new(
            CompositeWord::from_be_words([
                0x79be667ef9dcbbac,
                0x55a06295ce870b07,
                0x029bfcdb2dce28d9,
                0x59f2815b16f81798,
            ]),
            SECP256K1Mod,
        );
        let y = MontgomeryWord::new(
            CompositeWord::from_be_words([
                0x483ada7726a3c465,
                0x5da4fbfc0e1108a8,
                0xfd17b448a6855419,
                0x9c47d08ffb10d4b8,
            ]),
            SECP256K1Mod,
        );
        return self.unchecked_point_affine(x, y);
    }

    fn n(&self) -> CompositeWord<u64, 4> {
        return CompositeWord::from_be_words([
            0xffffffffffffffff,
            0xfffffffffffffffe,
            0xbaaedce6af48a03b,
            0xbfd25e8cd0364141,
        ]);
    }
}

#[test]
fn test_on_curve_const() {
    let curve = SECP256K1;
    let g = curve.g();
    assert!(
        g.is_affine(),
        "Base point g should be in affine coordinates"
    );
    assert!(
        curve.contains_const(g.coords()),
        "Base point g is not on the curve"
    );
}

#[test]
fn test_double_const() {
    let curve = SECP256K1;
    let g = curve.g();
    let g2 = g.double();
    assert!(curve.contains_const(g2.coords()), "2g is not on the curve");
    let g4 = g2.double();
    assert!(curve.contains_const(g4.coords()), "4g is not on the curve");
}

#[test]
fn test_neg_const() {
    let curve = SECP256K1;
    assert!(
        curve.zero().eq(-curve.zero()),
        "Negation of zero should be zero"
    );
    let g = curve.g();
    let neg_g = -g;
    assert!(
        curve.contains_const(neg_g.coords()),
        "-g is not on the curve"
    );
}

#[test]
fn test_add_const() {
    let curve = SECP256K1;
    let z = curve.zero();
    let g = curve.g();
    assert!((z + z).eq(z), "0 + 0 != 0");
    assert!((g + z).eq(g), "g + 0 != g");
    assert!((z + g).eq(g), "0 + g != g");
    assert!((g + -g).eq(curve.zero()), "g + (-g) != 0");
    assert!((-g + g).eq(curve.zero()), "(-g) + g != 0");
    let g2 = g.double();
    assert!((g + g).eq(g2), "g + g != 2g");
    assert!((g2 + g).eq(g + g2), "g2 + g != g + g2");
}

#[test]
fn test_mul_const() {
    let curve = SECP256K1;
    let z = curve.zero();
    let g = curve.g();
    fn scalar(n: u64) -> CompositeWord<u64, 4> {
        return CompositeWord::from_be_words([0, 0, 0, n]);
    }
    assert!((g * scalar(0)).eq(z), "g * 0 != 0");
    assert!((g * scalar(1)).eq(g), "g * 1 != g");
    assert!((g * scalar(2)).eq(g.double()), "g * 2 != 2g");
    assert!((g * scalar(3)).eq(g.double() + g), "g * 3 != 3g");
    assert!(
        (g * scalar(100)).eq(g.double() * scalar(50)),
        "g * 100 != 50 * (2g)"
    );
    assert!(
        (g * scalar(100)).eq((g.double() + g.double()) * scalar(25)),
        "g * 100 != 25 * (2g + 2g)"
    );
    assert!(
        (g * (curve.n().wrapping_sub(scalar(3)))).eq(-g.double() - g),
        "g * (n - 3) != -3g"
    );
    assert!(
        (g * (curve.n().wrapping_sub(scalar(2)))).eq(-g.double()),
        "g * (n - 2) != -2g"
    );
    assert!(
        (g * (curve.n().wrapping_sub(scalar(1)))).eq(-g),
        "g * (n - 1) != -g"
    );
    assert!((g * curve.n()).eq(z), "g * n != 0");
    assert!(
        (g * (curve.n().wrapping_add(scalar(1)))).eq(g),
        "g * (n + 1) != g"
    );
    assert!(
        (g * (curve.n().wrapping_add(scalar(2)))).eq(g.double()),
        "g * (n + 2) != 2g"
    );
}

#[test]
fn test_to_affine_const() {
    fn test_point(point: CurvePoint<u64, 4, SECP256K1>) {
        assert!(
            SECP256K1.contains_const(point.coords()),
            "Point is not on the curve"
        );
        let affine = point.to_affine();
        assert!(
            SECP256K1.contains_const(affine.coords()),
            "Affine point is not on the curve"
        );
        assert!(
            point.eq(affine),
            "Point should be equal to its affine representation"
        );
    }
    let g = SECP256K1.g();
    let g2 = g.double();
    test_point(SECP256K1.zero());
    test_point(g);
    test_point(-g);
    test_point(g2);
    test_point(g2 + g);
    test_point(g2 - g);
    test_point(g2 + g2);
    test_point(g2.to_affine() + g);
    test_point(g2.to_affine() - g);
    test_point(g2.to_affine() + g2);
    test_point(g2.to_affine() - g2);
}

macro_rules! test_func {
    ($func: ident, $($in_: ident,)* $(,)? $body:block) => {
        fn $func($($in_: CurvePoint<u64, 4, SECP256K1>,)*) {
            {
                type WP = OwnedFlexibleWordPool<usize>;
                struct TestCircuit {
                    $(
                        $in_: CurvePoint<u64, 4, SECP256K1>,
                    )*
                }
                impl Circuit for TestCircuit {
                    fn exec<B: Backend>(&self, frontend: &Frontend<B>) {
                        $(
                            let $in_ = self.$in_;
                        )*
                        let out = $body;
                        let out = frontend.point_alloc(out);
                        frontend.point_output_jacobian(out);
                    }
                }
                struct ExecCircuit {
                    $(
                        $in_: CurvePoint<u64, 4, SECP256K1>,
                    )*
                }
                impl Circuit for ExecCircuit {
                    fn exec<B: Backend>(&self, frontend: &Frontend<B>) {
                        $(
                            let $in_ = frontend.point_alloc(self.$in_);
                        )*
                        let out = $body;
                        frontend.point_output_jacobian(out);
                    }
                }
                let expected_outputs = exec::<_, WP>(&TestCircuit { $($in_,)* });
                let outputs = exec::<_, WP>(&ExecCircuit { $($in_,)* });
                assert_eq!(expected_outputs, outputs);
            }
        }
    };
}

/// Evaluate the data-oblivious `CurvePointRef::eq` (circuit version) on two points via the
/// execution backend, returning the resulting boolean as a `u8` (1 = equal, 0 = not equal).
fn eq_bit(a: CurvePoint<u64, 4, SECP256K1>, b: CurvePoint<u64, 4, SECP256K1>) -> u8 {
    type WP = OwnedFlexibleWordPool<usize>;
    struct EqCircuit {
        a: CurvePoint<u64, 4, SECP256K1>,
        b: CurvePoint<u64, 4, SECP256K1>,
    }
    impl Circuit for EqCircuit {
        fn exec<B: Backend>(&self, frontend: &Frontend<B>) {
            let a = frontend.point_alloc(self.a);
            let b = frontend.point_alloc(self.b);
            frontend.output(a.eq(b).into());
        }
    }
    return exec::<_, WP>(&EqCircuit { a, b }).u8[0];
}

#[test]
fn test_eq() {
    let curve = SECP256K1;
    let z = curve.zero();
    let g = curve.g();
    let g2 = g.double();

    // Spot-check the expected boolean directly.
    assert_eq!(eq_bit(g, g), 1, "g == g must be true");
    assert_eq!(eq_bit(z, z), 1, "0 == 0 must be true");
    assert_eq!(eq_bit(g, z), 0, "g == 0 must be false");
    assert_eq!(eq_bit(z, g), 0, "0 == g must be false");
    assert_eq!(eq_bit(g, g2), 0, "g == 2g must be false");
    assert_eq!(eq_bit(g, -g), 0, "g == -g must be false");
    // Representation-independence: a Jacobian point equals its affine form (different z, same point).
    assert_eq!(
        eq_bit(g2, g2.to_affine()),
        1,
        "2g (Jacobian) == 2g (affine) must be true"
    );
    assert_eq!(
        eq_bit(g2.to_affine(), g2),
        1,
        "2g (affine) == 2g (Jacobian) must be true"
    );

    // Exhaustively cross-check the circuit `eq` against the trusted cleartext `Point::eq` over a
    // spread of real secp256k1 points (finite, infinite, and mixed Jacobian/affine forms).
    let points = [
        z,
        g,
        -g,
        g2,
        g2.to_affine(),
        g2 + g,
        g2 - g,
        g2.double(),
        (g2 + g).to_affine(),
    ];
    for &a in &points {
        for &b in &points {
            let expected = a.eq(b) as u8;
            assert_eq!(
                eq_bit(a, b),
                expected,
                "circuit eq disagrees with cleartext Point::eq"
            );
        }
    }
}

#[test]
fn test_double() {
    test_func!(test_double, in_, { in_.double() });
    let zero = SECP256K1.zero();
    let g = SECP256K1.g();
    test_double(zero);
    test_double(g);
    test_double(g.double());
}

#[test]
fn test_neg() {
    test_func!(test_neg, in_, { -in_ });
    let zero = SECP256K1.zero();
    let g = SECP256K1.g();
    test_neg(zero);
    test_neg(g);
    test_neg(g.double());
}

#[test]
fn test_add() {
    test_func!(test_add, inl, inr, { inl + inr });
    let z = SECP256K1.zero();
    let g = SECP256K1.g();
    test_add(z, z);
    test_add(z, g);
    test_add(g, z);
    test_add(g, -g);
    test_add(-g, g);
    test_add(g, g);
    test_add(g.double(), g);
    test_add(g, g.double());
}

#[test]
fn test_to_affine() {
    test_func!(test_to_affine, in_, { in_.to_affine() });
    let g = SECP256K1.g();
    let g2 = g.double();
    test_to_affine(SECP256K1.zero());
    test_to_affine(g);
    test_to_affine(-g);
    test_to_affine(g2);
    test_to_affine(g2 + g);
    test_to_affine(g2 - g);
    test_to_affine(g2 + g2);
    test_to_affine(g2.to_affine() + g);
    test_to_affine(g2.to_affine() - g);
    test_to_affine(g2.to_affine() + g2);
    test_to_affine(g2.to_affine() - g2);
}
