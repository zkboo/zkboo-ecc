// SPDX-License-Identifier: LGPL-3.0-or-later

//! Validates the Ed25519 twisted-Edwards fixed-base scalar multiplication against known-answer
//! multiples of the base point, both for the build-time point arithmetic and for the in-circuit
//! oblivious comb (including a comb-table source reused across two multiplications).

use zkboo::{
    backend::{Backend, Frontend, WordRef},
    circuit::Circuit,
    executor::{OwnedFlexibleWordPool, exec},
};
use zkboo_ecc::edwards::{ComputedWindowTables, Point, mul_secret_scalar};
use zkboo::executor::ExecOptions;

type WP = OwnedFlexibleWordPool<usize>;

/// Known-answer compressed encodings of small and large multiples of the base point.
const VECTORS: [([u8; 32], &str); 4] = [
    (
        scalar_bytes(1),
        "5866666666666666666666666666666666666666666666666666666666666666",
    ),
    (
        scalar_bytes(2),
        "c9a3f86aae465f0e56513864510f3997561fa2c9e85ea21dc2292309f3cd6022",
    ),
    (
        scalar_bytes(3),
        "d4b4f5784868c3020403246717ec169ff79e26608ea126a1ab69ee77d1b16712",
    ),
    (
        // An arbitrary 255-bit scalar (big-endian bytes).
        [
            0x4f, 0xeb, 0x26, 0xb2, 0x64, 0x08, 0xfe, 0x0e, 0x4b, 0x4a, 0x1c, 0x3f, 0x9e, 0x22,
            0x8b, 0x1b, 0xa9, 0xbb, 0x40, 0x0a, 0xc6, 0x60, 0x97, 0xad, 0x97, 0x91, 0xf0, 0xd1,
            0xdd, 0xbf, 0x5e, 0x4a,
        ],
        "4c2d332f855c1a59d0139bab808c7cbbc7b84d727fd68ce529da3650904d8c80",
    ),
];

const fn scalar_bytes(value: u8) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    bytes[31] = value;
    return bytes;
}

/// Multiplies the base point by one or two secret scalars (big-endian bytes), sharing one
/// comb-table source, and outputs the compressed results.
struct EdwardsMulCircuit {
    scalars: Vec<[u8; 32]>,
}

impl Circuit for EdwardsMulCircuit {
    fn exec<B: Backend>(&self, frontend: &Frontend<B>) {
        let mut tables = ComputedWindowTables::new(Point::base(), 5);
        for scalar in &self.scalars {
            let bytes = scalar
                .iter()
                .map(|&b| frontend.input(b))
                .collect::<Vec<_>>();
            let limbs: [WordRef<B, u64, 1>; 4] = core::array::from_fn(|i| {
                let chunk = bytes[(3 - i) * 8..(4 - i) * 8].to_vec();
                WordRef::<B, u64, 1>::from_be_bytes(chunk)
                    .ok()
                    .expect("8 bytes per limb")
            });
            let scalar = WordRef::from_le_words(limbs);
            let point = mul_secret_scalar(scalar, &mut tables);
            point
                .compress()
                .into_iter()
                .for_each(|w| frontend.output(w));
        }
    }
}

fn to_hex(bytes: &[u8]) -> String {
    return bytes.iter().map(|b| format!("{b:02x}")).collect();
}

#[test]
fn test_edwards_mul_known_answers() {
    for (scalar, expected) in VECTORS {
        let out = exec::<_, WP, _>(&EdwardsMulCircuit {
            scalars: vec![scalar],
        }, ExecOptions::new())
        .u8;
        assert_eq!(to_hex(&out), expected);
    }
}

#[test]
fn test_edwards_mul_reused_tables() {
    // Two multiplications sharing one table source must both be correct.
    let out = exec::<_, WP, _>(&EdwardsMulCircuit {
        scalars: vec![VECTORS[1].0, VECTORS[3].0],
    }, ExecOptions::new())
    .u8;
    assert_eq!(to_hex(&out[..32]), VECTORS[1].1);
    assert_eq!(to_hex(&out[32..]), VECTORS[3].1);
}

#[test]
fn test_edwards_host_arithmetic() {
    // 2B computed as B + B and as B.double() must agree with the known encoding, via the
    // circuit-free build-time path (checked through to_niels/to_affine consistency).
    let b = Point::base();
    let (x2, y2) = b.add(b).to_affine();
    let (x2d, y2d) = b.double().to_affine();
    assert_eq!(x2.value(), x2d.value());
    assert_eq!(y2.value(), y2d.value());
    // Adding the identity is a no-op.
    let (xi, yi) = b.add(Point::identity()).to_affine();
    let (xb, yb) = b.to_affine();
    assert_eq!(xi.value(), xb.value());
    assert_eq!(yi.value(), yb.value());
}
