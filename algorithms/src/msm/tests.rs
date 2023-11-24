// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::ops::{AddAssign, Mul, MulAssign};

use crate::msm::*;
use bincode::de;
use snarkvm_curves::{
    bls12_377::{Fr, G1Affine, G1Projective},
    edwards_bls12::{EdwardsAffine, EdwardsAffine384, EdwardsParameters384, EdwardsProjective384, FrParameters},
    templates::{short_weierstrass_jacobian::Projective, twisted_edwards_extended},
    traits::{AffineCurve, ProjectiveCurve},
};
use snarkvm_fields::{Field, Fp256, PrimeField, Zero};
use snarkvm_utilities::{
    rand::{TestRng, Uniform},
    BigInteger, BigInteger256, BitIteratorBE, ToBytes, Write,
};

fn naive_variable_base_msm<G: AffineCurve>(
    bases: &[G],
    scalars: &[<G::ScalarField as PrimeField>::BigInteger],
) -> G::Projective {
    let mut acc = G::Projective::zero();

    for (base, scalar) in bases.iter().zip(scalars.iter()) {
        acc += base.mul_bits(BitIteratorBE::new(*scalar));
    }
    acc
}

#[test]
fn test_inverse() {
    use rand::Rng;
    use snarkvm_curves::edwards_bls12::FrParameters253;
    let mut rng = TestRng::default();
    let mut input_z = std::fs::File::create(format!("input_z.txt")).expect("create failed");
    let mut output_zinv = std::fs::File::create(format!("output_zinv.txt")).expect("create failed");

    let point_num = 1 << 3;
    let mut points: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
        (0..point_num).map(|_| rng.gen()).collect();
    for po in points.iter() {
        let tmp = po.clone();

        let z = tmp.z.to_bigint().to_biguint();

        writeln!(&input_z, "{:x}", z).unwrap();
        writeln!(&output_zinv, "{:x} ", tmp.z.inverse().unwrap().to_bigint().to_biguint()).unwrap();
        println!("z * z^-1 {:x}", (tmp.z.inverse().unwrap() * tmp.z).to_bigint().to_biguint());
    }
}

#[test]
fn test_mul() {
    // let mut points: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
    // (0..point_num).map(|_| rng.gen()).collect();
    use rand::Rng;
    use snarkvm_curves::edwards_bls12::FrParameters253;
    let mut rng = TestRng::default();

    let mut points: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
        (0..1).map(|_| rng.gen()).collect();

    let mut pe0_mul_2_point =
        points[0].clone() * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(2 as u64)).unwrap();
    let mut pe0_add_point = points[0].clone();
    pe0_add_point.add_assign(points[0]);

    assert_eq!(pe0_mul_2_point, pe0_add_point);
    println!("{:?}{:?}", pe0_mul_2_point, pe0_add_point);
}

#[test]
fn test_double_place() {
    // let mut points: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
    // (0..point_num).map(|_| rng.gen()).collect();
    use rand::Rng;
    use snarkvm_curves::edwards_bls12::FrParameters253;
    let mut rng = TestRng::default();

    let mut points: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
        (0..1).map(|_| rng.gen()).collect();

    let mut pe0_mul_2_point = points[0].clone();
    pe0_mul_2_point.double_in_place();
    let mut pe0_add_point = points[0].clone();
    pe0_add_point.add_assign(points[0]);

    assert_eq!(pe0_mul_2_point, pe0_add_point);
    println!("{:?}{:?}", pe0_mul_2_point, pe0_add_point);
}

#[test]
fn test_window_add() {
    for ind in 0..8 {
        use rand::Rng;
        use snarkvm_curves::edwards_bls12::FrParameters253;
        let mut rng = TestRng::default();

        // let mut pe_round0 = std::fs::File::create("in_pe_round0.txt").expect("create failed");
        // let mut pe_round1 = std::fs::File::create("in_pe_round1.txt").expect("create failed");
        // let mut pe_round2 = std::fs::File::create("in_pe_round2.txt").expect("create failed");
        // let mut pe_round3 = std::fs::File::create("in_pe_round3.txt").expect("create failed");

        // let mut pe_round0_sum = std::fs::File::create("mid_pe_round0_sum.txt").expect("create failed");
        // let mut pe_round1_sum = std::fs::File::create("mid_pe_round1_sum.txt").expect("create failed");
        // let mut pe_round2_sum = std::fs::File::create("mid_pe_round2_sum.txt").expect("create failed");
        // let mut pe_round3_sum = std::fs::File::create("mid_pe_round3_sum.txt").expect("create failed");

        // let mut pe_sum_all = std::fs::File::create("out_pe_sum_all.txt").expect("create failed");

        let mut input_pe = std::fs::File::create(format!("input_pe_{}.txt", ind)).expect("create failed");
        // let mut pe_round1 = std::fs::File::create(format!("in_pe_round1_{}.txt", ind)).expect("create failed");
        // let mut pe_round2 = std::fs::File::create(format!("in_pe_round2_{}.txt", ind)).expect("create failed");
        // let mut pe_round3 = std::fs::File::create(format!("in_pe_round3_{}.txt", ind)).expect("create failed");
        let mut pe_round0_sum = std::fs::File::create(format!("mid_pe_round0_sum_{}.txt", ind)).expect("create failed");
        let mut pe_round1_sum = std::fs::File::create(format!("mid_pe_round1_sum_{}.txt", ind)).expect("create failed");
        let mut pe_round2_sum = std::fs::File::create(format!("mid_pe_round2_sum_{}.txt", ind)).expect("create failed");
        let mut pe_round3_sum = std::fs::File::create(format!("mid_pe_round3_sum_{}.txt", ind)).expect("create failed");
        let mut pe_sum_all = std::fs::File::create(format!("output_{}.txt", ind)).expect("create failed");
        let mut pe_sum_all2 = std::fs::File::create(format!("output2_{}.txt", ind)).expect("create failed");

        let mut pe0_mul_2 = std::fs::File::create(format!("pe0_mul_2_{}.txt", ind)).expect("create failed");

        let point_num = 1 << 5;
        let mut points: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
            (0..point_num).map(|_| rng.gen()).collect();

        // for po in points.iter() {
        //     let tmp = po.clone();
        //     let x = tmp.x.to_bigint().to_biguint();
        //     let y = tmp.y.to_bigint().to_biguint();
        //     let z = tmp.z.to_bigint().to_biguint();
        //     let t = tmp.t.to_bigint().to_biguint();
        //     writeln!(&input_pe, "{:x} {:x} {:x} {:x}", x, y, z, t).unwrap();
        // }
        for i in 0..32 {
            let tmp = points[31 - i].clone();
            let x = tmp.x.to_bigint().to_biguint();
            let y = tmp.y.to_bigint().to_biguint();
            let z = tmp.z.to_bigint().to_biguint();
            let t = tmp.t.to_bigint().to_biguint();
            writeln!(&input_pe, "{:x} {:x} {:x} {:x}", x, y, z, t).unwrap();
        }
        // let mut pe0_mul_2_point =
        //     points[0].clone() * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(2 as u64)).unwrap();
        let mut pe0_mul_2_point = points[0].clone();
        // pe0_mul_2_point.double_in_place();
        // let mut pe0_add_point = points[0].clone();
        // pe0_add_point.add_assign(points[0]);

        // assert_eq!(pe0_mul_2_point, pe0_add_point);

        for _ in 0..9 {
            // pe0_mul_2_point =
            //     pe0_mul_2_point * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(2 as u64)).unwrap();

            let x = pe0_mul_2_point.x.to_bigint().to_biguint();
            let y = pe0_mul_2_point.y.to_bigint().to_biguint();
            let z = pe0_mul_2_point.z.to_bigint().to_biguint();
            let t = pe0_mul_2_point.t.to_bigint().to_biguint();
            writeln!(&pe0_mul_2, "{:x} {:x} {:x} {:x}", x, y, z, t).unwrap();
            // pe0_mul_2_point =
            //     pe0_mul_2_point * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(2 as u64)).unwrap();
            pe0_mul_2_point.double_in_place();
        }
        // assert_eq!(
        //     pe0_mul_2_point,
        //     points[0] * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(1 << 9 as u64)).unwrap()
        // );
        // return;

        let mut pe_sum_point = EdwardsProjective384::zero();
        {
            let round = 3;
            let mut round_sum = EdwardsProjective384::zero();
            for pe in 0..8 {
                let mut temp_point = points[round * 8 + 7 - pe].clone();
                // round_sum =
                //     round_sum * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(1 << 8 as u64)).unwrap();
                for _ in 0..8 {
                    round_sum.double_in_place();
                }
                round_sum.add_assign(temp_point);
            }
            let x = round_sum.x.to_bigint().to_biguint();
            let y = round_sum.y.to_bigint().to_biguint();
            let z = round_sum.z.to_bigint().to_biguint();
            let t = round_sum.t.to_bigint().to_biguint();
            writeln!(&pe_round3_sum, "{:x} {:x} {:x} {:x}", x, y, z, t).unwrap();
            // pe_sum_point = pe_sum_point
            //     * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(1 << 32 as u64)).unwrap()
            //     * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(1 << 32 as u64)).unwrap();
            for _ in 0..64 {
                pe_sum_point.double_in_place();
            }
            pe_sum_point.add_assign(round_sum);
        }
        {
            let round = 2;
            let mut round_sum = EdwardsProjective384::zero();
            for pe in 0..8 {
                let mut temp_point = points[round * 8 + 7 - pe].clone();
                // round_sum =
                //     round_sum * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(1 << 8 as u64)).unwrap();
                for _ in 0..8 {
                    round_sum.double_in_place();
                }
                round_sum.add_assign(temp_point);
            }
            let x = round_sum.x.to_bigint().to_biguint();
            let y = round_sum.y.to_bigint().to_biguint();
            let z = round_sum.z.to_bigint().to_biguint();
            let t = round_sum.t.to_bigint().to_biguint();
            writeln!(&pe_round2_sum, "{:x} {:x} {:x} {:x}", x, y, z, t).unwrap();
            // pe_sum_point = pe_sum_point
            //     * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(1 << 32 as u64)).unwrap()
            //     * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(1 << 32 as u64)).unwrap();
            for _ in 0..64 {
                pe_sum_point.double_in_place();
            }
            pe_sum_point.add_assign(round_sum);
        }
        {
            let round = 1;
            let mut round_sum = EdwardsProjective384::zero();
            for pe in 0..8 {
                let mut temp_point = points[round * 8 + 7 - pe].clone();
                // round_sum =
                //     round_sum * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(1 << 8 as u64)).unwrap();
                for _ in 0..8 {
                    round_sum.double_in_place();
                }
                round_sum.add_assign(temp_point);
            }
            let x = round_sum.x.to_bigint().to_biguint();
            let y = round_sum.y.to_bigint().to_biguint();
            let z = round_sum.z.to_bigint().to_biguint();
            let t = round_sum.t.to_bigint().to_biguint();
            writeln!(&pe_round1_sum, "{:x} {:x} {:x} {:x}", x, y, z, t).unwrap();
            // pe_sum_point = pe_sum_point
            //     * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(1 << 32 as u64)).unwrap()
            //     * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(1 << 32 as u64)).unwrap();
            for _ in 0..64 {
                pe_sum_point.double_in_place();
            }
            pe_sum_point.add_assign(round_sum);
        }
        {
            let round = 0;
            let mut round_sum = EdwardsProjective384::zero();
            for pe in 0..8 {
                let mut temp_point = points[round * 8 + 7 - pe].clone();
                // round_sum =
                //     round_sum * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(1 << 8 as u64)).unwrap();
                for _ in 0..8 {
                    round_sum.double_in_place();
                }
                round_sum.add_assign(temp_point);
            }
            let x = round_sum.x.to_bigint().to_biguint();
            let y = round_sum.y.to_bigint().to_biguint();
            let z = round_sum.z.to_bigint().to_biguint();
            let t = round_sum.t.to_bigint().to_biguint();
            writeln!(&pe_round0_sum, "{:x} {:x} {:x} {:x}", x, y, z, t).unwrap();
            // pe_sum_point = pe_sum_point
            //     * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(1 << 32 as u64)).unwrap()
            //     * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(1 << 32 as u64)).unwrap();
            for _ in 0..64 {
                pe_sum_point.double_in_place();
            }
            pe_sum_point.add_assign(round_sum);
        }

        {
            let x = pe_sum_point.x.to_bigint().to_biguint();
            let y = pe_sum_point.y.to_bigint().to_biguint();
            let z = pe_sum_point.z.to_bigint().to_biguint();
            let t = pe_sum_point.t.to_bigint().to_biguint();
            writeln!(&pe_sum_all, "{:x} {:x} {:x} {:x}", x, y, z, t).unwrap();
        }
        {
            // let mut pe_sum_point2 = EdwardsProjective384::zero();
            let mut pe_sum_point2 = points[31].clone();
            {
                let x = pe_sum_point2.x.to_bigint().to_biguint();
                let y = pe_sum_point2.y.to_bigint().to_biguint();
                let z = pe_sum_point2.z.to_bigint().to_biguint();
                let t = pe_sum_point2.t.to_bigint().to_biguint();

                writeln!(&pe_sum_all2, "{:x} {:x} {:x} {:x}", x, y, z, t).unwrap();
            }
            for pe in 1..32 {
                // pe_sum_point2 *= Fp256::<FrParameters253>::from_bigint(BigInteger256::from(1 << 8 as u64)).unwrap();
                for _ in 0..8 {
                    pe_sum_point2.double_in_place();
                }
                pe_sum_point2.add_assign(points[31 - pe]);
                let x = pe_sum_point2.x.to_bigint().to_biguint();
                let y = pe_sum_point2.y.to_bigint().to_biguint();
                let z = pe_sum_point2.z.to_bigint().to_biguint();
                let t = pe_sum_point2.t.to_bigint().to_biguint();

                writeln!(&pe_sum_all2, "{:x} {:x} {:x} {:x}", x, y, z, t).unwrap();
            }
            assert_eq!(pe_sum_point, pe_sum_point2);
        }
    }
}

#[test]
fn test_point_add() {
    use rand::Rng;
    use snarkvm_curves::edwards_bls12::FrParameters253;
    let mut rng = TestRng::default();

    {
        let mut inputfile_x1 = std::fs::File::create("input_x1.txt").expect("create failed");
        let mut inputfile_y1 = std::fs::File::create("input_y1.txt").expect("create failed");
        let mut inputfile_z1 = std::fs::File::create("input_z1.txt").expect("create failed");
        let mut inputfile_t1 = std::fs::File::create("input_t1.txt").expect("create failed");
        let mut inputfile_x2 = std::fs::File::create("input_x2.txt").expect("create failed");
        let mut inputfile_y2 = std::fs::File::create("input_y2.txt").expect("create failed");
        let mut inputfile_z2 = std::fs::File::create("input_z2.txt").expect("create failed");
        let mut inputfile_t2 = std::fs::File::create("input_t2.txt").expect("create failed");
        let mut outputfile_x1 = std::fs::File::create("output_x1.txt").expect("create failed");
        let mut outputfile_y1 = std::fs::File::create("output_y1.txt").expect("create failed");
        let mut outputfile_z1 = std::fs::File::create("output_z1.txt").expect("create failed");
        let mut outputfile_t1 = std::fs::File::create("output_t1.txt").expect("create failed");
        let mut outputfile_affine_x = std::fs::File::create("output_add_affine_x.txt").expect("create failed");
        let mut outputfile_affine_y = std::fs::File::create("output_add_affine_y.txt").expect("create failed");

        let point_num = 1 << 14;
        let mut points1: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
            (0..point_num).map(|_| rng.gen()).collect();
        let points2: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
            (0..point_num).map(|_| rng.gen()).collect();

        for point1 in points1.iter() {
            // writeln!(&inputfile_x1, "{:x}", point1.x.to_bigint().to_biguint()).unwrap();
            // writeln!(&inputfile_y1, "{:x}", point1.y.to_bigint().to_biguint()).unwrap();
            // writeln!(&inputfile_z1, "{:x}", point1.z.to_bigint().to_biguint()).unwrap();
            // writeln!(&inputfile_t1, "{:x}", point1.t.to_bigint().to_biguint()).unwrap();
            let xy = point1.x * point1.y;
            let tz = point1.t * point1.z;
            assert_eq!(xy, tz);
        }
        for point2 in points2.iter() {
            // writeln!(&inputfile_x2, "{:x}", point2.x.to_bigint().to_biguint()).unwrap();
            // writeln!(&inputfile_y2, "{:x}", point2.y.to_bigint().to_biguint()).unwrap();
            // writeln!(&inputfile_z2, "{:x}", point2.z.to_bigint().to_biguint()).unwrap();
            // writeln!(&inputfile_t2, "{:x}", point2.t.to_bigint().to_biguint()).unwrap();
            let xy = point2.x * point2.y;
            let tz = point2.t * point2.z;
            assert_eq!(xy, tz);
        }
        for (p1, p2) in points1.iter_mut().zip(points2) {
            p1.add_assign(p2);
            // writeln!(&outputfile_x1, "{:x}", p1.x.to_bigint().to_biguint()).unwrap();
            // writeln!(&outputfile_y1, "{:x}", p1.y.to_bigint().to_biguint()).unwrap();
            // writeln!(&outputfile_z1, "{:x}", p1.z.to_bigint().to_biguint()).unwrap();
            // writeln!(&outputfile_t1, "{:x}", p1.t.to_bigint().to_biguint()).unwrap();
            // writeln!(&outputfile_affine_x, "{:x}", p1.to_affine().x.to_bigint().to_biguint()).unwrap();
            // writeln!(&outputfile_affine_y, "{:x}", p1.to_affine().y.to_bigint().to_biguint()).unwrap();
        }
    }
    // {
    //     let mut mix_inputfile_x1 = std::fs::File::create("mix_input_x1.txt").expect("create failed");
    //     let mut mix_inputfile_y1 = std::fs::File::create("mix_input_y1.txt").expect("create failed");
    //     let mut mix_inputfile_z1 = std::fs::File::create("mix_input_z1.txt").expect("create failed");
    //     let mut mix_inputfile_t1 = std::fs::File::create("mix_input_t1.txt").expect("create failed");
    //     let mut mix_inputfile_x2 = std::fs::File::create("mix_input_x2.txt").expect("create failed");
    //     let mut mix_inputfile_y2 = std::fs::File::create("mix_input_y2.txt").expect("create failed");
    //     // let mut mix_inputfile_z2 = std::fs::File::create("mix_input_z2.txt").expect("create failed");
    //     // let mut mix_inputfile_t2 = std::fs::File::create("mix_input_t2.txt").expect("create failed");
    //     let mut mix_outputfile_x1 = std::fs::File::create("mix_output_x1.txt").expect("create failed");
    //     let mut mix_outputfile_y1 = std::fs::File::create("mix_output_y1.txt").expect("create failed");
    //     let mut mix_outputfile_z1 = std::fs::File::create("mix_output_z1.txt").expect("create failed");
    //     let mut mix_outputfile_t1 = std::fs::File::create("mix_output_t1.txt").expect("create failed");
    //     let mut mix_outputfile_affine_x = std::fs::File::create("mix_output_affine_x.txt").expect("create failed");
    //     let mut mix_outputfile_affine_y = std::fs::File::create("mix_output_affine_y.txt").expect("create failed");

    //     let point_num = 1 << 14;
    //     let mut points1: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
    //         (0..point_num).map(|_| rng.gen()).collect();
    //     let points2: Vec<twisted_edwards_extended::Affine<EdwardsParameters384>> =
    //         (0..point_num).map(|_| rng.gen()).collect();

    //     for point1 in points1.iter() {
    //         writeln!(&mix_inputfile_x1, "{:x}", point1.x.to_bigint().to_biguint()).unwrap();
    //         writeln!(&mix_inputfile_y1, "{:x}", point1.y.to_bigint().to_biguint()).unwrap();
    //         writeln!(&mix_inputfile_z1, "{:x}", point1.z.to_bigint().to_biguint()).unwrap();
    //         writeln!(&mix_inputfile_t1, "{:x}", point1.t.to_bigint().to_biguint()).unwrap();
    //     }
    //     for point2 in points2.iter() {
    //         writeln!(&mix_inputfile_x2, "{:x}", point2.x.to_bigint().to_biguint()).unwrap();
    //         writeln!(&mix_inputfile_y2, "{:x}", point2.y.to_bigint().to_biguint()).unwrap();
    //         // writeln!(&mix_inputfile_z2, "{:x}", point2.z.to_bigint().to_biguint()).unwrap();
    //         // writeln!(&mix_inputfile_t2, "{:x}", point2.t.to_bigint().to_biguint()).unwrap();
    //     }
    //     for (p1, p2) in points1.iter_mut().zip(points2) {
    //         p1.add_assign_mixed(&p2);
    //         writeln!(&mix_outputfile_x1, "{:x}", p1.x.to_bigint().to_biguint()).unwrap();
    //         writeln!(&mix_outputfile_y1, "{:x}", p1.y.to_bigint().to_biguint()).unwrap();
    //         writeln!(&mix_outputfile_z1, "{:x}", p1.z.to_bigint().to_biguint()).unwrap();
    //         writeln!(&mix_outputfile_t1, "{:x}", p1.t.to_bigint().to_biguint()).unwrap();
    //         writeln!(&mix_outputfile_affine_x, "{:x}", p1.to_affine().x.to_bigint().to_biguint()).unwrap();
    //         writeln!(&mix_outputfile_affine_y, "{:x}", p1.to_affine().y.to_bigint().to_biguint()).unwrap();
    //     }
    // }
}

#[test]
fn test_projective_add() {
    use rand::Rng;
    use snarkvm_curves::bls12_377::Fq;
    use snarkvm_curves::edwards_bls12::FrParameters253;
    use snarkvm_fields::One;
    let mut rng = TestRng::default();
    let degree = 1 << 5;
    let points1: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
        (0..degree).map(|_| rng.gen()).collect();

    let points2: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
        (0..degree).map(|_| rng.gen()).collect();

    for i in 0..degree {
        let mut add1 = points1[i].clone();
        add1.add_assign(points2[i]);
        let mut add2 = points1[i].clone();
        add2.add_assign_mixed(&points2[i].to_affine());
        // assert_eq!(add1.x, add2.x);
        println!("{:?} {:?}", add1.x, add2.x);
    }
}

#[test]
fn test_msmn() {
    use rand::Rng;
    use snarkvm_curves::bls12_377::Fq;
    use snarkvm_curves::edwards_bls12::FrParameters253;
    use snarkvm_fields::One;
    let mut rng = TestRng::default();
    for iter in 0..1 {
        let mut inputfile_x = std::fs::File::create(format!("input_x_{}.txt", iter)).expect("create failed");
        let mut inputfile_y = std::fs::File::create(format!("input_y_{}.txt", iter)).expect("create failed");
        // let mut inputfile_z = std::fs::File::create(format!("input_z_{}.txt", iter)).expect("create failed");
        // let mut inputfile_t = std::fs::File::create(format!("input_t_{}.txt", iter)).expect("create failed");
        let mut inputfile_te_x = std::fs::File::create(format!("input_te_x_{}.txt", iter)).expect("create failed");
        let mut inputfile_te_y = std::fs::File::create(format!("input_te_y_{}.txt", iter)).expect("create failed");
        let mut scalarfile = std::fs::File::create(format!("scalar_{}.txt", iter)).expect("create failed");
        let mut outputfile = std::fs::File::create(format!("output_{}.txt", iter)).expect("create failed");
        // let mut outputfile_affine: std::fs::File =
        //     std::fs::File::create(format!("output_affine_{}.txt", iter)).expect("create failed");
        let mut peoutputfile = std::fs::File::create(format!("peoutput_{}.txt", iter)).expect("create failed");

        // let mut inputfile_x = std::fs::File::create("input_x.txt").expect("create failed");
        // let mut inputfile_y = std::fs::File::create("input_y.txt").expect("create failed");
        // let mut scalarfile = std::fs::File::create("scalar.txt").expect("create failed");
        // let mut outputfile = std::fs::File::create("output.txt").expect("create failed");
        // let mut outputfile_affine = std::fs::File::create("output_affine.txt").expect("create failed");
        // let mut bucketfile = std::fs::File::create("bucket.txt").expect("create failed");

        let degree = 1 << 13;
        let bases_affine: Vec<twisted_edwards_extended::Affine<EdwardsParameters384>> =
            (0..degree).map(|_| rng.gen()).collect();

        for base in bases_affine.iter() {
            // let base_affine = base.to_affine().clone();
            // writeln!(&inputfile_a_x, "{:x}", base.x.to_bigint().to_biguint()).unwrap();
            // writeln!(&inputfile_a_y, "{:x}", base.y.to_bigint().to_biguint()).unwrap();

            let base_porject = base.clone();

            writeln!(&inputfile_te_x, "{:x}", base_porject.x.to_bigint().to_biguint()).unwrap();
            writeln!(&inputfile_te_y, "{:x}", base_porject.y.to_bigint().to_biguint()).unwrap();

            writeln!(&inputfile_x, "{:x}", base_porject.to_sw_affine().x.to_bigint().to_biguint()).unwrap();
            writeln!(&inputfile_y, "{:x}", base_porject.to_sw_affine().y.to_bigint().to_biguint()).unwrap();
            // writeln!(&inputfile_z, "{:x}", base_porject.z.to_bigint().to_biguint()).unwrap();
            // writeln!(&inputfile_t, "{:x}", base_porject.t.to_bigint().to_biguint()).unwrap();
        }
        let bases: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
            bases_affine.iter().map(|base| base.clone().to_projective()).collect();

        let mut scalars_fr: Vec<snarkvm_curves::edwards_bls12::Fr253> = bases.iter().map(|_| rng.gen()).collect();
        let mut scalars: Vec<BigInteger256> = scalars_fr.iter().map(|s| s.to_bigint()).collect();
        for s in scalars.iter() {
            writeln!(&scalarfile, "{:x}", s.to_biguint()).unwrap();
        }
        println!("{:x}", scalars[0].to_biguint());

        let scalaru8: Vec<Vec<u8>> = scalars.iter().map(|s| s.to_bytes_le().unwrap()).collect();

        for su8 in &scalaru8[0] {
            print!("{:02x}", su8);
        }
        println!();

        let commitment: twisted_edwards_extended::Projective<EdwardsParameters384> =
            VariableBase::msm(&bases_affine, &scalars);
        println!("commitment {:?}", commitment.to_affine());
        println!("commitment {:?}", commitment.to_affine().to_sw_affine());
        

        // print bucket
        let mut pevec: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> = Vec::new();
        for pei in 0..32 {
            print!("{:02x}", scalaru8[0][pei]);
            let mut peisum = twisted_edwards_extended::Projective::<EdwardsParameters384>::zero();
            for si in 0..scalaru8.len() {
                peisum.add_assign(
                    bases[si]
                        * snarkvm_curves::edwards_bls12::Fr253::from_bigint(BigInteger256::from(
                            scalaru8[si][pei] as u64,
                        ))
                        .unwrap(),
                );
            }
            // pesum = pesum * Fr::from_bigint(BigInteger256::from(1 << 8 as u64)).unwrap();
            // pesum.add_assign(peisum);
            pevec.push(peisum);
        }
        let mut pesum = twisted_edwards_extended::Projective::<EdwardsParameters384>::zero();
        for i in 0..32 {
            pesum = pesum * Fr::from_bigint(BigInteger256::from(1 << 8 as u64)).unwrap();
            pesum.add_assign(pevec[31 - i]);

            let base_porject = pevec[i].clone();
            let x = base_porject.x.to_bigint().to_biguint();
            let y = base_porject.y.to_bigint().to_biguint();
            let z = base_porject.z.to_bigint().to_biguint();
            let t = base_porject.t.to_bigint().to_biguint();
            writeln!(peoutputfile, "{:x} {:x} {:x} {:x}", x, y, z, t).unwrap();
        }

        assert_eq!(commitment.to_affine(), pesum.to_affine());
    }
}

#[test]
fn test_msm() {
    use rand::Rng;
    use snarkvm_curves::bls12_377::Fq;
    use snarkvm_curves::edwards_bls12::FrParameters253;
    use snarkvm_fields::One;
    let mut rng = TestRng::default();
    // let one = Fq::one();

    // println!("one {:?}", one.to_bigint());
    // let two = Fq::one() + Fq::one();
    // let three = Fq::one() + Fq::one() + Fq::one();

    for iter in 3..4 {
        // let iter = 0;
        let mut inputfile_x = std::fs::File::create(format!("input_x_{}.txt", iter)).expect("create failed");
        let mut inputfile_y = std::fs::File::create(format!("input_y_{}.txt", iter)).expect("create failed");
        let mut inputfile_z = std::fs::File::create(format!("input_z_{}.txt", iter)).expect("create failed");
        let mut inputfile_t = std::fs::File::create(format!("input_t_{}.txt", iter)).expect("create failed");
        let mut inputfile_a_x = std::fs::File::create(format!("input_affine_x_{}.txt", iter)).expect("create failed");
        let mut inputfile_a_y = std::fs::File::create(format!("input_affine_y_{}.txt", iter)).expect("create failed");
        let mut scalarfile = std::fs::File::create(format!("scalar_{}.txt", iter)).expect("create failed");
        let mut outputfile = std::fs::File::create(format!("output_{}.txt", iter)).expect("create failed");
        let mut outputfile_affine =
            std::fs::File::create(format!("output_affine_{}.txt", iter)).expect("create failed");
        let mut bucketfile1 = std::fs::File::create(format!("bucket1_{}.txt", iter)).expect("create failed");
        let mut bucket_mid_file1 = std::fs::File::create(format!("bucket_mid_{}.txt", iter)).expect("create failed");
        let mut bucket_mid_affinefile1 =
            std::fs::File::create(format!("bucket_mid_affine_{}.txt", iter)).expect("create failed");
        let mut bucketfile2 = std::fs::File::create(format!("bucket2_{}.txt", iter)).expect("create failed");
        let mut bucketfile_affine1 =
            std::fs::File::create(format!("bucket_affine_1_{}.txt", iter)).expect("create failed");
        let mut bucketfile_affine2 =
            std::fs::File::create(format!("bucket_affine_2_{}.txt", iter)).expect("create failed");
        let mut bucket_sum_file =
            std::fs::File::create(format!("bucket_sum_file_{}.txt", iter)).expect("create failed");
        // let mut inputfile_x = std::fs::File::create("input_x.txt").expect("create failed");
        // let mut inputfile_y = std::fs::File::create("input_y.txt").expect("create failed");
        // let mut scalarfile = std::fs::File::create("scalar.txt").expect("create failed");
        // let mut outputfile = std::fs::File::create("output.txt").expect("create failed");
        // let mut outputfile_affine = std::fs::File::create("output_affine.txt").expect("create failed");
        // let mut bucketfile = std::fs::File::create("bucket.txt").expect("create failed");

        let degree = 1 << 13;
        let bases_affine: Vec<twisted_edwards_extended::Affine<EdwardsParameters384>> =
            (0..degree).map(|_| rng.gen()).collect();

        for base in bases_affine.iter() {
            // let base_affine = base.to_affine().clone();
            writeln!(&inputfile_a_x, "{:x}", base.x.to_bigint().to_biguint()).unwrap();
            writeln!(&inputfile_a_y, "{:x}", base.y.to_bigint().to_biguint()).unwrap();

            let base_porject = base.clone().to_projective();

            writeln!(&inputfile_x, "{:x}", base_porject.x.to_bigint().to_biguint()).unwrap();
            writeln!(&inputfile_y, "{:x}", base_porject.y.to_bigint().to_biguint()).unwrap();
            writeln!(&inputfile_z, "{:x}", base_porject.z.to_bigint().to_biguint()).unwrap();
            writeln!(&inputfile_t, "{:x}", base_porject.t.to_bigint().to_biguint()).unwrap();
        }
        let bases: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
            bases_affine.iter().map(|base| base.clone().to_projective()).collect();

        let mut scalars: Vec<BigInteger256> = Vec::new();
        let mut scalar_u8: Vec<u8> = Vec::new();

        if iter == 0 {
            // fix scalar
            let s = rng.gen::<u8>();
            scalar_u8 = (0..degree).map(|_| s).collect();

            // let scalar_u8: Vec<u8> = (0..degree).map(|_| rng.gen::<u8>()).collect();
            scalars = scalar_u8.iter().map(|s| BigInteger256::from(*s as u64)).collect();
            for s in scalar_u8.iter() {
                writeln!(&scalarfile, "{:x}", s).unwrap();
            }
        } else if iter == 1 {
            // scalar: 0~200
            scalar_u8 = (0..degree).map(|_| rng.gen_range(0..200)).collect();

            // let scalar_u8: Vec<u8> = (0..degree).map(|_| rng.gen::<u8>()).collect();
            scalars = scalar_u8.iter().map(|s| BigInteger256::from(*s as u64)).collect();
            for s in scalar_u8.iter() {
                writeln!(&scalarfile, "{:x}", s).unwrap();
            }
        } else if iter == 2 {
            // scalar: 0~100
            scalar_u8 = (0..degree).map(|_| rng.gen_range(0..100)).collect();

            // let scalar_u8: Vec<u8> = (0..degree).map(|_| rng.gen::<u8>()).collect();
            scalars = scalar_u8.iter().map(|s| BigInteger256::from(*s as u64)).collect();
            for s in scalar_u8.iter() {
                writeln!(&scalarfile, "{:x}", s).unwrap();
            }
        } else if iter == 3 {
            // scalar: 0~100
            scalar_u8 = (0..degree).map(|_| rng.gen::<u8>()).collect();

            // let scalar_u8: Vec<u8> = (0..degree).map(|_| rng.gen::<u8>()).collect();
            scalars = scalar_u8.iter().map(|s| BigInteger256::from(*s as u64)).collect();
            for s in scalar_u8.iter() {
                writeln!(&scalarfile, "{:x}", s).unwrap();
            }
        }
        // // fix scalar
        // let s = rng.gen::<u8>();
        // let scalar_u8: Vec<u8> = (0..degree).map(|_| s).collect();

        // // let scalar_u8: Vec<u8> = (0..degree).map(|_| rng.gen::<u8>()).collect();
        // let scalars: Vec<BigInteger256> = scalar_u8.iter().map(|s| BigInteger256::from(*s as u64)).collect();
        // for s in scalar_u8.iter() {
        //     writeln!(&scalarfile, "{:x}", s).unwrap();
        // }

        // let commitment: twisted_edwards_extended::Affine<EdwardsParameters384> =
        //     VariableBase::msm(&bases, &scalars);
        // println!("commitment {:?}", commitment.to_affine());

        // print bucket
        let bucket_size = 1 << 8;
        let mut bucket_point = vec![twisted_edwards_extended::Projective::<EdwardsParameters384>::zero(); bucket_size];
        for i in 0..degree {
            let index = scalar_u8[i] as usize;
            bucket_point[index].add_assign(&bases[i]);

            if index == 2 {
                let x = bucket_point[2].x.to_bigint().to_biguint();
                let y = bucket_point[2].y.to_bigint().to_biguint();
                let z = bucket_point[2].z.to_bigint().to_biguint();
                let t = bucket_point[2].t.to_bigint().to_biguint();
                writeln!(&bucket_mid_file1, "{:x} {:x} {:x} {:x}", x, y, z, t).unwrap();
                writeln!(
                    &bucket_mid_affinefile1,
                    "{:x} {:x}",
                    bucket_point[2].to_affine().x.to_bigint().to_biguint(),
                    bucket_point[2].to_affine().y.to_bigint().to_biguint()
                )
                .unwrap();
            }
        }
        for buck in bucket_point.iter() {
            let bucket = buck.clone();
            let x1 = bucket.to_affine().x.to_bigint().to_biguint();
            let y1 = bucket.to_affine().y.to_bigint().to_biguint();
            let x = bucket.x.to_bigint().to_biguint();
            let y = bucket.y.to_bigint().to_biguint();
            let z = bucket.z.to_bigint().to_biguint();
            let t = bucket.t.to_bigint().to_biguint();
            writeln!(&bucketfile1, "{:x} {:x} {:x} {:x}", x, y, z, t).unwrap();
            writeln!(&bucketfile_affine1, "{:x} {:x}", x1, y1).unwrap();
        }
        // sum all the bucket
        let mut bucket_sum = twisted_edwards_extended::Projective::<EdwardsParameters384>::zero();
        for i in 0..bucket_size {
            let mul_bucket =
                bucket_point[i] * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(i as u64)).unwrap();

            let x1 = mul_bucket.to_affine().x.to_bigint().to_biguint();
            let y1 = mul_bucket.to_affine().y.to_bigint().to_biguint();

            let x = mul_bucket.x.to_bigint().to_biguint();
            let y = mul_bucket.y.to_bigint().to_biguint();
            let z = mul_bucket.z.to_bigint().to_biguint();
            let t = mul_bucket.t.to_bigint().to_biguint();

            writeln!(&bucketfile2, "{:x} {:x} {:x} {:x}", x, y, z, t).unwrap();
            writeln!(&bucketfile_affine2, "{:x} {:x}", x1, y1).unwrap();

            bucket_sum.add_assign(&mul_bucket);
        }

        println!(
            "{:x} {:x}",
            bucket_sum.to_affine().x.to_bigint().to_biguint(),
            bucket_sum.to_affine().y.to_bigint().to_biguint(),
        );
        println!(
            "{:x} {:x} {:x} {:x}",
            bucket_sum.x.to_bigint().to_biguint(),
            bucket_sum.y.to_bigint().to_biguint(),
            bucket_sum.t.to_bigint().to_biguint(),
            bucket_sum.z.to_bigint().to_biguint()
        );
        writeln!(
            outputfile,
            "{:x} {:x} {:x} {:x}",
            bucket_sum.x.to_bigint().to_biguint(),
            bucket_sum.y.to_bigint().to_biguint(),
            bucket_sum.z.to_bigint().to_biguint(),
            bucket_sum.t.to_bigint().to_biguint()
        )
        .unwrap();
        writeln!(
            outputfile_affine,
            "{:x} {:x} ",
            bucket_sum.to_affine().x.to_bigint().to_biguint(),
            bucket_sum.to_affine().y.to_bigint().to_biguint(),
        )
        .unwrap();
    }
}

#[test]
fn test_msm2() {
    use rand::Rng;
    use snarkvm_curves::bls12_377::Fq;
    use snarkvm_curves::edwards_bls12::FrParameters253;
    use snarkvm_fields::One;
    let mut rng = TestRng::default();
    // let one = Fq::one();

    // println!("one {:?}", one.to_bigint());
    // let two = Fq::one() + Fq::one();
    // let three = Fq::one() + Fq::one() + Fq::one();

    {
        // let iter = 0;

        let degree = 1 << 13;
        let bases_affine: Vec<twisted_edwards_extended::Affine<EdwardsParameters384>> =
            (0..degree).map(|_| rng.gen()).collect();

        let bases: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
            bases_affine.iter().map(|base| base.clone().to_projective()).collect();

        let mut scalars: Vec<BigInteger256> = Vec::new();

        // let scalar_u8: Vec<u8> = (0..degree).map(|_| rng.gen::<u8>()).collect();
        use snarkvm_curves::edwards_bls12::Fr253;
        let mut scalars: Vec<Fr253> = (0..degree).map(|_| rng.gen::<Fr253>()).collect();
        let mut scalars: Vec<BigInteger256> = scalars.iter().map(|s| s.to_bigint()).collect();

        let commitment: twisted_edwards_extended::Projective<EdwardsParameters384> =
            VariableBase::msm(&bases_affine, &scalars);
        println!("commitment {:?}", commitment.to_affine());
    }
}
#[test]
fn test_zero_trans() {
    // let te_points = EdwardsAffine384::zero();
    // let sw_points = te_points.to_sw_affine();
    // println!("{:?}", sw_points);
    // let te_points2 = sw_points.to_te_affine();
    // println!("{:?}", te_points2);

    let sw_points = G1Affine::zero();
    println!("{:?}", sw_points);
    let te_points2 = sw_points.to_te_affine();
    println!("{:?}", te_points2);
    println!("{:?}", te_points2.is_zero());
}

#[test]
fn test_zero_add() {
    use rand::Rng;
    use snarkvm_curves::edwards_bls12::FrParameters253;
    let mut rng = TestRng::default();

    {
        let mut inputfile_x1 = std::fs::File::create("input_x1.txt").expect("create failed");
        let mut inputfile_y1 = std::fs::File::create("input_y1.txt").expect("create failed");
        let mut inputfile_z1 = std::fs::File::create("input_z1.txt").expect("create failed");
        let mut inputfile_t1 = std::fs::File::create("input_t1.txt").expect("create failed");
        let mut inputfile_x2 = std::fs::File::create("input_x2.txt").expect("create failed");
        let mut inputfile_y2 = std::fs::File::create("input_y2.txt").expect("create failed");
        let mut inputfile_z2 = std::fs::File::create("input_z2.txt").expect("create failed");
        let mut inputfile_t2 = std::fs::File::create("input_t2.txt").expect("create failed");
        let mut outputfile_x1 = std::fs::File::create("output_x1.txt").expect("create failed");
        let mut outputfile_y1 = std::fs::File::create("output_y1.txt").expect("create failed");
        let mut outputfile_z1 = std::fs::File::create("output_z1.txt").expect("create failed");
        let mut outputfile_t1 = std::fs::File::create("output_t1.txt").expect("create failed");
        let mut outputfile_affine_x = std::fs::File::create("output_add_affine_x.txt").expect("create failed");
        let mut outputfile_affine_y = std::fs::File::create("output_add_affine_y.txt").expect("create failed");

        let point_num = 1 << 10;
        let mut points1: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
            (0..point_num).map(|_| rng.gen()).collect();
        // let points2: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
        //     (0..point_num).map(|_| twisted_edwards_extended::Projective::<EdwardsParameters384>::zero()).collect();
        let points2: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
            (0..point_num).map(|_| rng.gen()).collect();

        for point1 in points1.iter() {
            writeln!(&inputfile_x1, "{:x}", point1.x.to_bigint().to_biguint()).unwrap();
            writeln!(&inputfile_y1, "{:x}", point1.y.to_bigint().to_biguint()).unwrap();
            writeln!(&inputfile_z1, "{:x}", point1.z.to_bigint().to_biguint()).unwrap();
            writeln!(&inputfile_t1, "{:x}", point1.t.to_bigint().to_biguint()).unwrap();
            // let xy = point1.x * point1.y;
            // let tz = point1.t * point1.z;
            // assert_eq!(xy, tz);
        }
        for point2 in points1.iter() {
            writeln!(&inputfile_x2, "{:x}", point2.x.to_bigint().to_biguint()).unwrap();
            writeln!(&inputfile_y2, "{:x}", point2.y.to_bigint().to_biguint()).unwrap();
            writeln!(&inputfile_z2, "{:x}", point2.z.to_bigint().to_biguint()).unwrap();
            writeln!(&inputfile_t2, "{:x}", point2.t.to_bigint().to_biguint()).unwrap();
            let xy = point2.x * point2.y;
            let tz = point2.t * point2.z;
            assert_eq!(xy, tz);
        }
        for (p1, p2) in points1.iter_mut().zip(points2) {
            // let mut temp  = p1.clone() *  Fp256::<FrParameters253>::from_bigint(BigInteger256::from(2 as u64)).unwrap();
            let mut temp = p1.clone();
            temp.double_in_place();

            let mut temp2 = p1.clone();
            temp2.add_assign(p1);

            assert_eq!(temp, temp2);
            println!("{:x}  {:x}", temp.z.to_bigint().to_biguint(), temp2.z.to_bigint().to_biguint());

            writeln!(&outputfile_x1, "{:x}", temp.x.to_bigint().to_biguint()).unwrap();
            writeln!(&outputfile_y1, "{:x}", temp.y.to_bigint().to_biguint()).unwrap();
            writeln!(&outputfile_z1, "{:x}", temp.z.to_bigint().to_biguint()).unwrap();
            writeln!(&outputfile_t1, "{:x}", temp.t.to_bigint().to_biguint()).unwrap();
            writeln!(&outputfile_affine_x, "{:x}", temp.to_affine().x.to_bigint().to_biguint()).unwrap();
            writeln!(&outputfile_affine_y, "{:x}", temp.to_affine().y.to_bigint().to_biguint()).unwrap();
        }
    }
}

#[test]
fn test_sw_2_te() {
    use rand::Rng;
    // use snarkvm_curves::bls12_377::Fq;
    // use snarkvm_curves::edwards_bls12::FrParameters253;
    // use snarkvm_fields::One;
    let mut rng = TestRng::default();
    {
        let mut te_file = std::fs::File::create(format!("te.txt")).expect("create failed");
        let mut te_affine_file = std::fs::File::create(format!("te_affine.txt")).expect("create failed");
        let mut sw_file = std::fs::File::create(format!("sw.txt")).expect("create failed");
        let mut te2_file = std::fs::File::create(format!("sw->te.txt")).expect("create failed");

        let degree = 1;
        let tw_points: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
            (0..degree).map(|_| rng.gen()).collect();

        for point in tw_points {
            let x = point.x.to_bigint().to_biguint();
            let y = point.y.to_bigint().to_biguint();
            let z = point.z.to_bigint().to_biguint();
            let t = point.t.to_bigint().to_biguint();
            writeln!(&te_file, "{:x} {:x} {:x} {:x}", x, y, z, t).unwrap();

            let affine_point = point.to_affine();
            let affine_x = affine_point.x.to_bigint().to_biguint();
            let affine_y = affine_point.y.to_bigint().to_biguint();

            writeln!(&te_affine_file, "{:x} {:x} ", affine_x, affine_y).unwrap();

            let sw_affine = point.to_affine().to_sw_affine();
            let sw_x = sw_affine.x.to_bigint().to_biguint();
            let sw_y = sw_affine.y.to_bigint().to_biguint();
            writeln!(&sw_file, "{:x} {:x} ", sw_x, sw_y).unwrap();

            let te2 = sw_affine.to_te_affine().to_projective();
            // let te2_x = te2.x.to_bigint().to_biguint();
            // let te2_y = te2.y.to_bigint().to_biguint();
            // let te2_t = te2.t.to_bigint().to_biguint();
            // let te2_z = te2.z.to_bigint().to_biguint();
            // writeln!(&te2_file, "{:x} {:x} {:x} {:x}", te2_x, te2_y, te2_t, te2_z).unwrap();
        }
    }

    // use rand::Rng;
    // use snarkvm_curves::bls12_377::Fq;
    // use snarkvm_fields::One;

    // let mut rng = TestRng::default();
    // let one = Fq::one();

    // println!("one {:?}", one.to_bigint());
    // let two = Fq::one() + Fq::one();
    // let three = Fq::one() + Fq::one() + Fq::one();

    // let a: twisted_edwards_extended::Affine<EdwardsParameters384> = rng.gen();

    // let one256: snarkvm_fields::Fp256<snarkvm_curves::edwards_bls12::FqParameters> = Fr::one();
    // let two256 = Fr::one() + Fr::one();
    // let three256 = Fr::one() + Fr::one() + Fr::one();

    // let mut bases1 = Vec::new();
    // let mut bases2 = Vec::new();
    // let mut scalars = Vec::new();
    // for _ in 0..1024 {
    //     let a: twisted_edwards_extended::Affine<EdwardsParameters384> = rng.gen();
    //     bases1.push(a);
    //     bases2.push(a.to_sw_affine());
    //     let s: Fp256<FrParameters> = rng.gen();
    //     println!("{:?}", s);
    //     scalars.push(s.to_bigint());
    // }

    // let commitment = VariableBase::msm(&bases1, &scalars);
    // // println!("commitment {:?}", commitment);
    // // let point = commitment.to_affine();
    // // let a = twisted_edwards_extended::Affine::<EdwardsParameters384>::new();
    // // let sw_point: twisted_edwards_extended::Affine<EdwardsParameters384> = rng.gen();
    // // let sw_point = sw_point.to_sw_affine();

    // let sw_commit = VariableBase::msm(&bases2, &scalars);
    // let sw_te_commit = sw_commit.to_affine().to_te_affine();

    // let commitment = commitment.to_affine();
    // println!("{:?}", commitment);
    // println!("{:?}", sw_te_commit);
    // assert_eq!(commitment, sw_te_commit);
}

#[test]
fn variable_base_test_with_bls12() {
    const SAMPLES: usize = 1 << 10;

    let mut rng = TestRng::default();

    let v = (0..SAMPLES).map(|_| Fr::rand(&mut rng).to_bigint()).collect::<Vec<_>>();
    let g = (0..SAMPLES).map(|_| G1Projective::rand(&mut rng).to_affine()).collect::<Vec<_>>();

    let naive = naive_variable_base_msm(g.as_slice(), v.as_slice());
    let fast = VariableBase::msm(g.as_slice(), v.as_slice());

    assert_eq!(naive.to_affine(), fast.to_affine());
}

#[test]
fn variable_base_test_with_bls12_unequal_numbers() {
    const SAMPLES: usize = 1 << 10;

    let mut rng = TestRng::default();

    let v = (0..SAMPLES - 100).map(|_| Fr::rand(&mut rng).to_bigint()).collect::<Vec<_>>();
    let g = (0..SAMPLES).map(|_| G1Projective::rand(&mut rng).to_affine()).collect::<Vec<_>>();

    let naive = naive_variable_base_msm(g.as_slice(), v.as_slice());
    let fast = VariableBase::msm(g.as_slice(), v.as_slice());

    assert_eq!(naive.to_affine(), fast.to_affine());
}
