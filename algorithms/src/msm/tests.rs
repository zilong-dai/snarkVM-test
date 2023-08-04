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

use std::ops::AddAssign;

use crate::msm::*;
use snarkvm_curves::{
    bls12_377::{Fr, G1Affine, G1Projective},
    edwards_bls12::{EdwardsParameters384, FrParameters},
    templates::twisted_edwards_extended,
    traits::{AffineCurve, ProjectiveCurve},
};
use snarkvm_fields::{Fp256, PrimeField, Zero};
use snarkvm_utilities::{
    rand::{TestRng, Uniform},
    BigInteger, BigInteger256, BitIteratorBE, Write,
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
            let tz = point1.t*point1.z;
            assert_eq!(xy, tz);
        }
        for point2 in points2.iter() {
            // writeln!(&inputfile_x2, "{:x}", point2.x.to_bigint().to_biguint()).unwrap();
            // writeln!(&inputfile_y2, "{:x}", point2.y.to_bigint().to_biguint()).unwrap();
            // writeln!(&inputfile_z2, "{:x}", point2.z.to_bigint().to_biguint()).unwrap();
            // writeln!(&inputfile_t2, "{:x}", point2.t.to_bigint().to_biguint()).unwrap();
            let xy = point2.x * point2.y;
            let tz = point2.t*point2.z;
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

    {
        let iter = 0;
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
        let mut bucketfile2 = std::fs::File::create(format!("bucket2_{}.txt", iter)).expect("create failed");
        // let mut inputfile_x = std::fs::File::create("input_x.txt").expect("create failed");
        // let mut inputfile_y = std::fs::File::create("input_y.txt").expect("create failed");
        // let mut scalarfile = std::fs::File::create("scalar.txt").expect("create failed");
        // let mut outputfile = std::fs::File::create("output.txt").expect("create failed");
        // let mut outputfile_affine = std::fs::File::create("output_affine.txt").expect("create failed");
        // let mut bucketfile = std::fs::File::create("bucket.txt").expect("create failed");

        let degree = 1 << 10;
        let bases: Vec<twisted_edwards_extended::Affine<EdwardsParameters384>> =
            (0..degree).map(|_| rng.gen()).collect();

        for base in bases.iter() {
            writeln!(&inputfile_a_x, "{:x}", base.x.to_bigint().to_biguint()).unwrap();
            writeln!(&inputfile_a_y, "{:x}", base.y.to_bigint().to_biguint()).unwrap();

            let base_porject = base.to_projective();

            writeln!(&inputfile_x, "{:x}", base_porject.x.to_bigint().to_biguint()).unwrap();
            writeln!(&inputfile_y, "{:x}", base_porject.y.to_bigint().to_biguint()).unwrap();
            writeln!(&inputfile_z, "{:x}", base_porject.z.to_bigint().to_biguint()).unwrap();
            writeln!(&inputfile_t, "{:x}", base_porject.t.to_bigint().to_biguint()).unwrap();
        }

        let scalar_u8: Vec<u8> = (0..degree).map(|_| rng.gen::<u8>()).collect();
        let scalars: Vec<BigInteger256> = scalar_u8.iter().map(|s| BigInteger256::from(*s as u64)).collect();
        for s in scalar_u8.iter() {
            writeln!(&scalarfile, "{:x}", s).unwrap();
        }

        let commitment: twisted_edwards_extended::Projective<EdwardsParameters384> =
            VariableBase::msm(&bases, &scalars);
        println!("commitment {:?}", commitment.to_affine());

        // print bucket
        let bucket_size = 1 << 8;
        let mut bucket_point = vec![twisted_edwards_extended::Projective::<EdwardsParameters384>::zero(); bucket_size];
        for i in 0..degree {
            let index = scalar_u8[i] as usize;
            bucket_point[index].add_assign_mixed(&bases[i]);
        }
        for bucket in bucket_point.iter() {
            let x = bucket.x.to_bigint().to_biguint();
            let y = bucket.y.to_bigint().to_biguint();
            let z = bucket.z.to_bigint().to_biguint();
            let t = bucket.t.to_bigint().to_biguint();
            writeln!(&bucketfile1, "{:x} {:x} {:x} {:x}", x, y, t, z).unwrap();
        }
        // sum all the bucket
        let mut bucket_sum = twisted_edwards_extended::Projective::<EdwardsParameters384>::zero();
        for i in 0..bucket_size {
            let mul_bucket =
                bucket_point[i] * Fp256::<FrParameters253>::from_bigint(BigInteger256::from(i as u64)).unwrap();

            let x = mul_bucket.x.to_bigint().to_biguint();
            let y = mul_bucket.y.to_bigint().to_biguint();
            let z = mul_bucket.z.to_bigint().to_biguint();
            let t = mul_bucket.t.to_bigint().to_biguint();
            writeln!(&bucketfile2, "{:x} {:x} {:x} {:x}", x, y, t, z).unwrap();

            bucket_sum.add_assign_mixed(&mul_bucket.to_affine());
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
            bucket_sum.t.to_bigint().to_biguint(),
            bucket_sum.z.to_bigint().to_biguint()
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


        let degree = 1 << 4;
        let tw_points: Vec<twisted_edwards_extended::Projective<EdwardsParameters384>> =
            (0..degree).map(|_| rng.gen()).collect();
        
        for point in tw_points {
            let x = point.x.to_bigint().to_biguint();
            let y = point.y.to_bigint().to_biguint();
            let z = point.z.to_bigint().to_biguint();
            let t = point.t.to_bigint().to_biguint();
            writeln!(&te_file, "{:x} {:x} {:x} {:x}", x, y, t, z).unwrap();

            let affine_point = point.to_affine();
            let affine_x = affine_point.x.to_bigint().to_biguint();
            let affine_y = affine_point.y.to_bigint().to_biguint();

            writeln!(&te_affine_file, "{:x} {:x} ", affine_x, affine_y).unwrap();

            let sw_affine = point.to_affine().to_sw_affine();
            let sw_x = sw_affine.x.to_bigint().to_biguint();
            let sw_y = sw_affine.y.to_bigint().to_biguint();
            writeln!(&sw_file, "{:x} {:x} ", sw_x, sw_y).unwrap();

            let te2 = sw_affine.to_te_affine().to_projective();
            let te2_x = te2.x.to_bigint().to_biguint();
            let te2_y = te2.y.to_bigint().to_biguint();
            let te2_t = te2.t.to_bigint().to_biguint();
            let te2_z = te2.z.to_bigint().to_biguint();
            writeln!(&te2_file, "{:x} {:x} {:x} {:x}", te2_x, te2_y, te2_t, te2_z).unwrap();
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
