// SPDX-License-Identifier: LGPL-3.0-or-later

//! The secp256k1 curve, as used by Bitcoin and Ethereum, implemented with 4×u64 limbs.

use crate::weierstrass::{Curve, Point};
use zkboo::word::CompositeWord;
use zkboo_modular::montgomery::{MontgomeryMod, MontgomeryWord};
use zkboo_modular::pseudo_mersenne::PseudoMersenneMod;

/// The secp256k1 base field modulus `p = 2^256 - 2^32 - 977`, as a [MontgomeryMod].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Secp256k1Field;

impl MontgomeryMod<u64, 4> for Secp256k1Field {
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

/// The secp256k1 curve `y² = x³ + 7`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Secp256k1;

impl Curve<u64, 4> for Secp256k1 {
    type P = Secp256k1Field;

    fn p(&self) -> Self::P {
        return Secp256k1Field;
    }

    fn a(&self) -> MontgomeryWord<u64, 4, Self::P> {
        return MontgomeryWord::new(CompositeWord::from_be_words([0, 0, 0, 0]), Secp256k1Field);
    }

    fn b(&self) -> MontgomeryWord<u64, 4, Self::P> {
        return MontgomeryWord::new(CompositeWord::from_be_words([0, 0, 0, 7]), Secp256k1Field);
    }

    fn g(&self) -> Point<u64, 4, Self> {
        let x = MontgomeryWord::new(
            CompositeWord::from_be_words([
                0x79be667ef9dcbbac,
                0x55a06295ce870b07,
                0x029bfcdb2dce28d9,
                0x59f2815b16f81798,
            ]),
            Secp256k1Field,
        );
        let y = MontgomeryWord::new(
            CompositeWord::from_be_words([
                0x483ada7726a3c465,
                0x5da4fbfc0e1108a8,
                0xfd17b448a6855419,
                0x9c47d08ffb10d4b8,
            ]),
            Secp256k1Field,
        );
        return self.unchecked_point_affine(x, y);
    }

    fn n(&self) -> CompositeWord<u64, 4> {
        // The group order n.
        return CompositeWord::from_be_words([
            0xffffffffffffffff,
            0xfffffffffffffffe,
            0xbaaedce6af48a03b,
            0xbfd25e8cd0364141,
        ]);
    }
}

/// The secp256k1 base field modulus as a pseudo-Mersenne (Solinas) field: `p = 2^256 - c` with `c =
/// 2^32 + 977`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Secp256k1FieldPM;

impl PseudoMersenneMod<u64, 4> for Secp256k1FieldPM {
    #[inline]
    fn p(&self) -> CompositeWord<u64, 4> {
        return Secp256k1Field.n();
    }
    #[inline]
    fn c(&self) -> CompositeWord<u64, 4> {
        // 2^256 - p = 2^32 + 977
        return CompositeWord::from_be_words([0, 0, 0, 0x0000_0001_0000_03d1]);
    }
}

zkboo_modular::impl_pseudo_mersenne_field_rep!(Secp256k1FieldPM, u64, 4);

/// The secp256k1 curve `y² = x³ + 7` over the pseudo-Mersenne field [Secp256k1FieldPM].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Secp256k1PM;

impl Curve<u64, 4> for Secp256k1PM {
    type P = Secp256k1FieldPM;

    fn p(&self) -> Self::P {
        return Secp256k1FieldPM;
    }

    fn a(&self) -> MontgomeryWord<u64, 4, Self::P> {
        return MontgomeryWord::new(CompositeWord::from_be_words([0, 0, 0, 0]), Secp256k1FieldPM);
    }

    fn b(&self) -> MontgomeryWord<u64, 4, Self::P> {
        return MontgomeryWord::new(CompositeWord::from_be_words([0, 0, 0, 7]), Secp256k1FieldPM);
    }

    fn g(&self) -> Point<u64, 4, Self> {
        let x = MontgomeryWord::new(
            CompositeWord::from_be_words([
                0x79be667ef9dcbbac,
                0x55a06295ce870b07,
                0x029bfcdb2dce28d9,
                0x59f2815b16f81798,
            ]),
            Secp256k1FieldPM,
        );
        let y = MontgomeryWord::new(
            CompositeWord::from_be_words([
                0x483ada7726a3c465,
                0x5da4fbfc0e1108a8,
                0xfd17b448a6855419,
                0x9c47d08ffb10d4b8,
            ]),
            Secp256k1FieldPM,
        );
        return self.unchecked_point_affine(x, y);
    }

    fn n(&self) -> CompositeWord<u64, 4> {
        return Secp256k1.n();
    }
}
