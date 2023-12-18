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

#![forbid(unsafe_code)]
#![allow(clippy::too_many_arguments)]
#![warn(clippy::cast_possible_truncation)]

mod helpers;
pub use helpers::*;

mod hash;
use hash::*;

#[cfg(test)]
mod tests;

use console::{
    account::Address,
    prelude::{anyhow, bail, cfg_iter, ensure, has_duplicates, Network, Result, ToBytes},
    program::cfg_into_iter, network::Testnet3, types::Scalar,
};
use snarkvm_algorithms::{
    fft::{DensePolynomial, EvaluationDomain},
    polycommit::kzg10::{UniversalParams as SRS, KZG10, KZGCommitment}, msm::VariableBase,
};
use snarkvm_curves::{PairingEngine, ProjectiveCurve, templates::twisted_edwards_extended::{Affine, Projective}, edwards_bls12::{EdwardsParameters384}, bls12_377::{G1Affine, Bls12_377G1Parameters, Fr}, AffineCurve};
use snarkvm_fields::{PrimeField, Zero, One, Fp256};
use snarkvm_synthesizer_snark::UniversalSRS;
use snarkvm_utilities::{cfg_zip_fold, BigInteger, BigInteger256, FromBits, FromBytes};

use aleo_std::prelude::*;
use std::{sync::Arc, time::Instant, ops::AddAssign};

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

#[derive(Clone)]
pub enum CoinbasePuzzle<N: Network> {
    /// The prover contains the coinbase puzzle proving key.
    Prover(Arc<CoinbaseProvingKey<N>>),
    /// The verifier contains the coinbase puzzle verifying key.
    Verifier(Arc<CoinbaseVerifyingKey<N>>),
}
impl CoinbasePuzzle<Testnet3>{
    pub fn precompute3(
        &self,
        epoch_challenge: &EpochChallenge<Testnet3>,
    ) -> Result<Vec<Affine<EdwardsParameters384>>> {
        let pk: &Arc<CoinbaseProvingKey<Testnet3>> = match self {
            Self::Prover(coinbase_proving_key) => coinbase_proving_key,
            Self::Verifier(_) => bail!("Cannot prove the coinbase puzzle with a verifier"),
        };
        let precompute_msm_start = Instant::now();
        let c_evaluations = epoch_challenge.epoch_polynomial_evaluations().evaluations.clone();

        let pk_lag_basis = pk.lagrange_basis_at_beta_g.clone();
        let mut c_g = Vec::new();
        for i in 0..c_evaluations.len() {
            c_g.push(pk_lag_basis[i] * c_evaluations[i]);
        }
        let precompute_msm_duration = precompute_msm_start.elapsed();
        println!("Time elapsed in precompute msm() is: {:?}", precompute_msm_duration);

        let precompute_fft_start = Instant::now();
        pk.product_domain.fft_in_place(&mut c_g);
        let precompute_fft_duration = precompute_fft_start.elapsed();
        println!("Time elapsed in precompute fft() is: {:?}", precompute_fft_duration);

        let mut ghat = vec![Affine::<EdwardsParameters384>::zero();c_g.len()];
        for i in 0..c_g.len() / 2 {
            let point = c_g[i].clone().to_affine().to_te_affine();
            let mut point128 = point.clone().to_projective();
            for _ in 0..128{
                point128.double_in_place();
            }

            ghat[i] = point128.to_affine();
            ghat[i + c_g.len() / 2] = point;
        }
        Ok(ghat)
    }

    pub fn prove3(
        &self,
        epoch_challenge: &EpochChallenge<Testnet3>,
        address: Address<Testnet3>,
        nonce: u64,
        minimum_proof_target: Option<u64>,
    ) -> Result<(u32, PartialSolution<Testnet3>)> {
        let pk: &Arc<CoinbaseProvingKey<Testnet3>> = match self {
            Self::Prover(coinbase_proving_key) => coinbase_proving_key,
            Self::Verifier(_) => bail!("Cannot prove the coinbase puzzle with a verifier"),
        };

        let ghat: Vec<Affine<EdwardsParameters384>> = self.precompute3(epoch_challenge).unwrap();

        let polynomial: DensePolynomial<_> = Self::prover_polynomial(epoch_challenge, address, nonce).unwrap();
        // let polynomial = epoch_challenge.epoch_polynomial().clone();
        let bases = ghat.clone();

        // let scalars: Vec<Fp256<snarkvm_curves::edwards_bls12::FrParameters>> = polynomial.coeffs.iter().map(|poly| {println!("{:?}", poly); Fp256::<snarkvm_curves::edwards_bls12::FrParameters>::from_bigint(poly.0).unwrap()}).collect();
        use snarkvm_curves::edwards_bls12::Fr253;
        let scalars: Vec<Fr253> = polynomial.coeffs.clone();
        // println!("poly f scalar {:?}", scalars);
        let scalars = scalars.iter().map(|s| s.to_bigint()).collect::<Vec<_>>();

        let mut commitment = VariableBase::msm(&bases, &scalars);

        println!("commitment sw {:?}", commitment.to_affine().to_sw_affine());

        let (random_commit, _rand) = KZG10::generate_random_commit(&pk.lagrange_basis(), None, None)?;
        println!("random_commit {:?}", random_commit);
        // println!("random_commit te {:?}", random_commit.to_te_affine());
        commitment.add_assign_mixed(&random_commit.to_te_affine());
        println!("commitment sw {:?}", commitment.to_affine().to_sw_affine());
        println!("commitment sw {:x}", commitment.to_affine().to_sw_affine().x.to_bigint().to_biguint());
        println!("commitment sw {:x}", commitment.to_affine().to_sw_affine().y.to_bigint().to_biguint());

        // println!("final commitment {:?}", commitment.to_affine().to_sw_affine());

        // println!("commitment2 {:?}", commitment.to_affine());

        let commitment = KZGCommitment(commitment.to_affine().to_sw_affine());

        let partial_solution = PartialSolution::new(address, nonce, commitment);
        // println!("proof_target {:?}", partial_solution.to_target().unwrap());
        // Check that the minimum target is met.
        if let Some(minimum_target) = minimum_proof_target {
            let proof_target = partial_solution.to_target()?;
            ensure!(
                proof_target >= minimum_target,
                "Prover solution was below the necessary proof target ({proof_target} < {minimum_target})"
            );
        }

        Ok((epoch_challenge.epoch_number(), partial_solution))
    }

    pub fn prove4(
        &self,
        ghat: Vec<Affine<EdwardsParameters384>>,
        epoch_challenge: &EpochChallenge<Testnet3>,
        address: Address<Testnet3>,
        nonce: u64,
        minimum_proof_target: Option<u64>,
        rep: u64,
    ) -> Result<(u32, PartialSolution<Testnet3>)> {
        let pk: &Arc<CoinbaseProvingKey<Testnet3>> = match self {
            Self::Prover(coinbase_proving_key) => coinbase_proving_key,
            Self::Verifier(_) => bail!("Cannot prove the coinbase puzzle with a verifier"),
        };

        // let precompute_start = Instant::now();
        // let ghat: Vec<Affine<EdwardsParameters384>> = self.precompute3(epoch_challenge).unwrap();

        use std::io::Write;

        // for gh in ghat.iter() {
        //     let point = gh.clone();
        //     let x = point.x.to_bigint().to_biguint();
        //     let y = point.y.to_bigint().to_biguint();
        //     // let z = point.z.to_bigint().to_biguint();
        //     // let t = point.t.to_bigint().to_biguint();
        //     // writeln!(&input_poly_file, "{:x} {:x} {:x} {:x}", x, y, z, t).unwrap();
        //     writeln!(&input_x_file, "{:x}", x).unwrap();
        //     writeln!(&input_y_file, "{:x}", y).unwrap();
        // }

        // let ghat2: Vec<Affine<EdwardsParameters384>> = ghat.iter().map(|g| g.to_te_affine()).collect();
        // println!("ghat {:?}", ghat2);

        // let precompute_duration = precompute_start.elapsed();
        // println!("Time elapsed in precompute() is: {:?}", precompute_duration);
        // println!("precompute: {:?}", ghat2.iter().map(|g| g.to_sw_affine()).collect::<Vec<G1Affine>>());

        let miner_start: Instant = Instant::now();
        let polynomial: DensePolynomial<_> = Self::prover_polynomial(epoch_challenge, address, nonce).unwrap();

        // let polynomial = epoch_challenge.epoch_polynomial().clone();
        let bases = ghat.clone();

        // let scalars: Vec<Fp256<snarkvm_curves::edwards_bls12::FrParameters>> = polynomial.coeffs.iter().map(|poly| {println!("{:?}", poly); Fp256::<snarkvm_curves::edwards_bls12::FrParameters>::from_bigint(poly.0).unwrap()}).collect();
        use snarkvm_curves::edwards_bls12::Fr253;
        let scalars: Vec<Fr253> = polynomial.coeffs.clone();
        println!("poly f scalar {:?}", scalars[0]);

        let mut scalarsfile = std::fs::File::create(format!("scalars_{}.txt", rep)).expect("create failed");

        for s in scalars.iter() {
            writeln!(scalarsfile, "{:x}", s.clone().to_bigint().to_biguint()).unwrap();
        }

        println!("scalars[0] {:x}", scalars[0].to_bigint().to_biguint());

        let scalars = scalars.iter().map(|s| s.to_bigint()).collect::<Vec<_>>();

        let mut commitment = VariableBase::msm(&bases, &scalars);
        println!("prove4 commitment sw {:?}", commitment.to_affine().to_sw_affine());

        let commitment2 = Projective::<EdwardsParameters384>::zero();

        let bases2 = ghat.clone();


        for i in 0..scalars.len(){
            // println!("{:x}", scalars[i].clone().to_biguint());
            // TODO 
            use snarkvm_curves::AffineCurve;
            let mut b128 = bases[i].clone().to_projective();
            for _ in 0..128{
                b128.double_in_place();
            }
            let mut tempa1 = Projective::<EdwardsParameters384>::zero();
            let mut tempa2 = Projective::<EdwardsParameters384>::zero();
            let s = scalars[i].clone().to_bytes_le().unwrap();
            // for su8 in s.clone(){
            //     print!("{:02x} ", su8);
            // }
            // println!();

            for j in 0..16{
                tempa1 = tempa1 * Fr::from_bigint(BigInteger256::from(1 << 8 as u64)).unwrap();
                tempa2 = tempa2 * Fr::from_bigint(BigInteger256::from(1 << 8 as u64)).unwrap();
                tempa1.add_assign(bases[i] * Fr::from_bigint(BigInteger256::from(s[15 - j] as u64)).unwrap());
                tempa2.add_assign(b128* Fr::from_bigint(BigInteger256::from(s[31 - j] as u64)).unwrap());
            }
            let tmp = bases[i].clone() * Fr::from_bigint(scalars[i].clone()).unwrap() ;
            let mut temp = Projective::<EdwardsParameters384>::zero();
            for j in 0..32{
                for _ in 0..8{
                    temp.double_in_place();
                }
                
                temp.add_assign(bases[i].clone() * Fr::from_bigint(BigInteger256::from(s[31 - j] as u64)).unwrap());
               
            }
            assert_eq!(tmp, tempa1+ tempa2);
            assert_eq!(tmp.to_affine(), temp.to_affine());
        }
        // let mut commitmentcomp = commitment.clone();
        // let mut add_point = Projective::<EdwardsParameters384>::zero();
        // for (i, base) in bases.clone().iter().enumerate() {
        //     add_point.add_assign(
        //             base.clone() * snarkvm_curves::edwards_bls12::Fr253::from_bigint(BigInteger256::from((i % 8) as u64)).unwrap(),
        //     );
        // }
        // for _ in 0..253{
        //     add_point.double_in_place();
        // }
        // println!("add_point {:?}", add_point.to_affine());
        // commitmentcomp.add_assign(add_point);

        // {
        //     let one = Fr253::one();
        //     let mut two = one + one;

        //     let mut twopower253 = one.clone();
        //     for _ in 0..253{
        //         twopower253 = twopower253*two;
        //     }

        //     let scalars2 = polynomial.coeffs.clone().iter().enumerate().map(|(i, s)| (*s + twopower253 * Fr253::from_bigint(BigInteger256::from(i as u64 % 8)).unwrap()).to_bigint()  ).collect::<Vec<_>>();
        //     let mut commitment2 = VariableBase::msm(&bases, &scalars2);

        //     let unscalars = polynomial.coeffs.clone().iter().enumerate().map(|(i, _s)| (twopower253 * Fr253::from_bigint(BigInteger256::from(i as u64 % 8)).unwrap()).to_bigint()  ).collect::<Vec<_>>();
        //     let mut commitment3 = VariableBase::msm(&bases, &scalars2);
        //     assert_eq!(commitment + commitment3, commitment2);
        // }

        // let mut commitment = Projective::<EdwardsParameters384>::zero();
        // for i in 0..ghat.len() {
        //     commitment.add_assign(ghat[i] * scalars[i]);
        // }
        // println!("commitment sw1 {:?}", VariableBase::msm(&ghat, &scalars).to_affine().to_te_affine());
        // println!("commitment te {:?}", commitment.to_affine());
        // println!("commitment sw {:?}", commitment.to_affine().to_sw_affine());
        // println!("commitment te2 {:?}", commitment.to_affine().to_sw_affine().to_te_affine());
        // let mut peoutputfile = std::fs::File::create(format!("peoutput_{}.txt", rep)).expect("create failed");

        // let scalaru8: Vec<Vec<u8>> = scalars.iter().map(|s| s.to_bytes_le().unwrap()).collect();

        // let mut pevec: Vec<Projective<EdwardsParameters384>> = Vec::new();
        // let mut subpoint : Projective<EdwardsParameters384> = Projective::<EdwardsParameters384>::zero();
        // for pei in 0..32 {
        //     print!("{:02x}", scalaru8[0][pei]);
        //     let mut peisum = Projective::<EdwardsParameters384>::zero();
        //     for si in 0..scalaru8.len() {
        //         peisum.add_assign(
        //             bases[si]
        //                 * snarkvm_curves::edwards_bls12::Fr253::from_bigint(BigInteger256::from(
        //                     scalaru8[si][pei] as u64,
        //                 ))
        //                 .unwrap(),
        //         );
        //         if pei == 31 {

        //             peisum.add_assign(
        //                 bases[si]
        //                     * snarkvm_curves::edwards_bls12::Fr253::from_bigint(BigInteger256::from(
        //                         (si % 8) as u64 *32,
        //                     ))
        //                     .unwrap(),
        //             );
        //             subpoint.add_assign(bases[si] * snarkvm_curves::edwards_bls12::Fr253::from_bigint(BigInteger256::from((si %8)as u64 *32)).unwrap());
        //         }
        //     }
        //     // pesum = pesum * Fr::from_bigint(BigInteger256::from(1 << 8 as u64)).unwrap();
        //     // pesum.add_assign(peisum);
        //     pevec.push(peisum);
        // }
        // let mut pesum = Projective::<EdwardsParameters384>::zero();
        // for i in 0..32 {
        //     pesum = pesum * Fr::from_bigint(BigInteger256::from(1 << 8 as u64)).unwrap();
        //     pesum.add_assign(pevec[31 - i]);

        //     let base_porject = pevec[i].clone();
        //     let x = base_porject.x.to_bigint().to_biguint();
        //     let y = base_porject.y.to_bigint().to_biguint();
        //     let z = base_porject.z.to_bigint().to_biguint();
        //     let t = base_porject.t.to_bigint().to_biguint();
        //     writeln!(peoutputfile, "{:x} {:x} {:x} {:x}", x, y, z, t).unwrap();
        // }
        // for _ in 0..248{
        //     subpoint.double_in_place();
        // }
        // pesum.add_assign(-subpoint);

        // assert_eq!(commitment.to_affine(), pesum.to_affine());

        let (random_commit, _rand) = KZG10::generate_random_commit(&pk.lagrange_basis(), None, None)?;
        println!("random_commit {:?}", random_commit);
        // println!("random_commit te {:?}", random_commit.to_te_affine());
        commitment.add_assign_mixed(&random_commit.to_te_affine());
        // println!("final commitment {:?}", commitment.to_affine().to_sw_affine());
        let miner_duration = miner_start.elapsed();
        // println!("Time elapsed in compute() is: {:?}", miner_duration);
        // let commitment = commitment - commitment;
        // {
        //     let point = commitment.clone();
        //     let x = point.x.to_bigint().to_biguint();
        //     let y = point.y.to_bigint().to_biguint();
        //     let z = point.z.to_bigint().to_biguint();
        //     let t = point.t.to_bigint().to_biguint();
        //     println!("{:x} {:x} {:x} {:x}", x, y, z, t);
        //     println!("prove4 commitment te {:?}", commitment);
        //     println!("prove4 commitment sw {:?}", commitment.to_affine().to_sw_affine());
        // }

        let commitment = KZGCommitment(commitment.to_affine().to_sw_affine());

        println!("prove4 commitment {:?}", commitment.0);

        let partial_solution = PartialSolution::new(address, nonce, commitment);
        // println!("proof_target {:?}", partial_solution.to_target().unwrap());
        // Check that the minimum target is met.
        if let Some(minimum_target) = minimum_proof_target {
            let proof_target = partial_solution.to_target()?;
            println!("proof_target {:08x}", proof_target);
            ensure!(
                proof_target >= minimum_target,
                "Prover solution was below the necessary proof target ({proof_target} < {minimum_target})"
            );
        }

        Ok((epoch_challenge.epoch_number(), partial_solution))
    }
    
    // test 2<<14 points
    pub fn prove5(
        &self,
        ghat: Vec<Affine<EdwardsParameters384>>,
        epoch_challenge: &EpochChallenge<Testnet3>,
        address: Address<Testnet3>,
        nonce: u64,
        minimum_proof_target: Option<u64>,
        rep: u64,
    ) -> Result<(u32, PartialSolution<Testnet3>)> {
        let pk: &Arc<CoinbaseProvingKey<Testnet3>> = match self {
            Self::Prover(coinbase_proving_key) => coinbase_proving_key,
            Self::Verifier(_) => bail!("Cannot prove the coinbase puzzle with a verifier"),
        };

        // let precompute_start = Instant::now();
        // let ghat: Vec<Affine<EdwardsParameters384>> = self.precompute3(epoch_challenge).unwrap();

        use std::io::Write;



        let miner_start: Instant = Instant::now();
        let polynomial: DensePolynomial<_> = Self::prover_polynomial(epoch_challenge, address, nonce).unwrap();

        // let polynomial = epoch_challenge.epoch_polynomial().clone();
        let bases = ghat.clone();

        // let scalars: Vec<Fp256<snarkvm_curves::edwards_bls12::FrParameters>> = polynomial.coeffs.iter().map(|poly| {println!("{:?}", poly); Fp256::<snarkvm_curves::edwards_bls12::FrParameters>::from_bigint(poly.0).unwrap()}).collect();
        use snarkvm_curves::edwards_bls12::Fr253;
        let scalars: Vec<Fr253> = polynomial.coeffs.clone();

        let scalars = scalars.iter().map(|s| s.to_bigint()).collect::<Vec<_>>();
        // use snarkvm_utilities::Read;
        let mut scalars_lh =  vec![BigInteger256::from(0); bases.len()];
        for i in 0..bases.len()/2 {
            let sca = scalars[i].to_bytes_le().unwrap();
            let mut sh128 = sca.clone();
            let mut sl128 = sca.clone();
            for (i, s) in sh128.iter_mut().enumerate(){
                if i >= 16 {
                    *s = 0;
                }
            }
            // for (i, s) in sl128.iter_mut().rev().enumerate(){
            //     if i < 16 {
            //         *s = 0;
            //     }
            // }
            for i in 0..16{
                sl128[i] = sl128[16+i];
                sl128[16 + i] = 0;
            }
            // println!("{:x} ", scalars[i].to_biguint());
            let h128 = BigInteger256::read_le(&sl128[..]).unwrap();
            let l128 = BigInteger256::read_le(&sh128[..]).unwrap();
            // println!("{:x} {:x}", h128.to_biguint(), l128.to_biguint());
            scalars_lh[i] = h128;
            scalars_lh[i + bases.len()/2] = l128;
        }
        println!("{:x} ", scalars[0].to_biguint());
        println!("{:x} {:x} ", scalars_lh[0].to_biguint(), scalars_lh[scalars.len()].to_biguint());

        let mut commitment = VariableBase::msm(&bases, &scalars_lh);
        // println!("prove4 commitment sw {:?}", commitment.to_affine().to_sw_affine());

        let base2: Vec<Affine<EdwardsParameters384>> = bases.iter().enumerate().filter(|(i, _)| 2 * i >= bases.len()).map(|(i, s)| s.clone()).collect();
        let mut commitment2 = VariableBase::msm(&base2, &scalars);

        println!("{:?} ", bases[scalars.len()]);
        println!("{:?} ", base2[0]);

        assert_eq!(commitment, commitment2);
        let commitment = KZGCommitment(commitment.to_affine().to_sw_affine());

        let partsolution = PartialSolution::new(address, nonce, commitment);

        Ok((epoch_challenge.epoch_number(), partsolution))
    }
}

impl<N: Network> CoinbasePuzzle<N> {
    /// Initializes a new `SRS` for the coinbase puzzle.
    #[cfg(any(test, feature = "setup"))]
    pub fn setup(config: PuzzleConfig) -> Result<SRS<N::PairingCurve>> {
        // The SRS must support committing to the product of two degree `n` polynomials.
        // Thus, the SRS must support committing to a polynomial of degree `2n - 1`.
        let total_degree = (2 * config.degree - 1).try_into()?;
        let srs = KZG10::load_srs(total_degree)?;
        Ok(srs)
    }

    /// Load the coinbase puzzle proving and verifying keys.
    pub fn load() -> Result<Self> {
        let max_degree = N::COINBASE_PUZZLE_DEGREE;
        // Load the universal SRS.
        let universal_srs = UniversalSRS::<N>::load()?;
        // Trim the universal SRS to the maximum degree.
        Self::trim(&*universal_srs, PuzzleConfig { degree: max_degree })
    }

    pub fn trim(srs: &SRS<N::PairingCurve>, config: PuzzleConfig) -> Result<Self> {
        // As above, we must support committing to the product of two degree `n` polynomials.
        // Thus, the SRS must support committing to a polynomial of degree `2n - 1`.
        // Since the upper bound to `srs.powers_of_beta_g` takes as input the number
        // of coefficients. The degree of the product has `2n - 1` coefficients.
        //
        // Hence, we request the powers of beta for the interval [0, 2n].
        let product_domain = Self::product_domain(config.degree)?;

        let lagrange_basis_at_beta_g = srs.lagrange_basis(product_domain)?;
        let fft_precomputation = product_domain.precompute_fft();
        let product_domain_elements = product_domain.elements().collect();

        let vk = CoinbaseVerifyingKey::<N> {
            g: srs.power_of_beta_g(0)?,
            gamma_g: <N::PairingCurve as PairingEngine>::G1Affine::zero(), // We don't use gamma_g later on since we are not hiding.
            h: srs.h,
            beta_h: srs.beta_h(),
            prepared_h: srs.prepared_h.clone(),
            prepared_beta_h: srs.prepared_beta_h.clone(),
        };

        let pk = CoinbaseProvingKey {
            product_domain,
            product_domain_elements,
            lagrange_basis_at_beta_g,
            fft_precomputation,
            verifying_key: vk,
        };

        Ok(Self::Prover(Arc::new(pk)))
    }

    /// Returns a prover solution to the coinbase puzzle.
    pub fn prove(
        &self,
        epoch_challenge: &EpochChallenge<N>,
        address: Address<N>,
        nonce: u64,
        minimum_proof_target: Option<u64>,
    ) -> Result<ProverSolution<N>> {
        // Retrieve the coinbase proving key.
        let pk = match self {
            Self::Prover(coinbase_proving_key) => coinbase_proving_key,
            Self::Verifier(_) => bail!("Cannot prove the coinbase puzzle with a verifier"),
        };

        let polynomial = Self::prover_polynomial(epoch_challenge, address, nonce)?;

        let product_evaluations = {
            let polynomial_evaluations = pk.product_domain.in_order_fft_with_pc(&polynomial, &pk.fft_precomputation);
            pk.product_domain.mul_polynomials_in_evaluation_domain(
                polynomial_evaluations,
                &epoch_challenge.epoch_polynomial_evaluations().evaluations,
            )?
        };
        let (commitment, _rand) = KZG10::commit_lagrange(&pk.lagrange_basis(), &product_evaluations, None, None)?;

        let partial_solution = PartialSolution::new(address, nonce, commitment);
        
        // Check that the minimum target is met.
        if let Some(minimum_target) = minimum_proof_target {
            let proof_target = partial_solution.to_target()?;
            ensure!(
                proof_target >= minimum_target,
                "Prover solution was below the necessary proof target ({proof_target} < {minimum_target})"
            );
        }

        let point = hash_commitment(&commitment)?;
        let product_eval_at_point = polynomial.evaluate(point) * epoch_challenge.epoch_polynomial().evaluate(point);

        let proof = KZG10::open_lagrange(
            &pk.lagrange_basis(),
            pk.product_domain_elements(),
            &product_evaluations,
            point,
            product_eval_at_point,
        )?;
        ensure!(!proof.is_hiding(), "The prover solution must contain a non-hiding proof");

        debug_assert!(KZG10::check(&pk.verifying_key, &commitment, point, product_eval_at_point, &proof)?);

        Ok(ProverSolution::new(partial_solution, proof))
    }

    pub fn precompute(
        &self,
        epoch_challenge: &EpochChallenge<N>,
    ) -> Result<Vec<<N::PairingCurve as PairingEngine>::G1Affine>> {
        let pk: &Arc<CoinbaseProvingKey<N>> = match self {
            Self::Prover(coinbase_proving_key) => coinbase_proving_key,
            Self::Verifier(_) => bail!("Cannot prove the coinbase puzzle with a verifier"),
        };
        let precompute_msm_start = Instant::now();
        let c_evaluations = epoch_challenge.epoch_polynomial_evaluations().evaluations.clone();

        let pk_lag_basis = pk.lagrange_basis_at_beta_g.clone();
        let mut c_g: Vec<<N::PairingCurve as PairingEngine>::G1Projective> = Vec::new();
        for i in 0..c_evaluations.len() {
            c_g.push(pk_lag_basis[i] * c_evaluations[i]);
        }
        let precompute_msm_duration = precompute_msm_start.elapsed();
        println!("Time elapsed in precompute msm() is: {:?}", precompute_msm_duration);

        let precompute_fft_start = Instant::now();
        pk.product_domain.fft_in_place(&mut c_g);
        let precompute_fft_duration = precompute_fft_start.elapsed();
        println!("Time elapsed in precompute fft() is: {:?}", precompute_fft_duration);

        let mut ghat = Vec::new();
        for i in 0..c_evaluations.len() / 2 {
            ghat.push(c_g[i].clone().to_affine());
        }
        Ok(ghat)
    }

    pub fn prove2(
        &self,
        epoch_challenge: &EpochChallenge<N>,
        address: Address<N>,
        nonce: u64,
        minimum_proof_target: Option<u64>,
    ) -> Result<(u32, PartialSolution<N>)> {
        let pk: &Arc<CoinbaseProvingKey<N>> = match self {
            Self::Prover(coinbase_proving_key) => coinbase_proving_key,
            Self::Verifier(_) => bail!("Cannot prove the coinbase puzzle with a verifier"),
        };

        // let c_evaluations = epoch_challenge.epoch_polynomial_evaluations().evaluations.clone();

        // let pk_lag_basis = pk.lagrange_basis_at_beta_g.clone();
        // let mut c_g : Vec<<N::PairingCurve as PairingEngine>::G1Projective>  = Vec::new();
        // for i in 0..c_evaluations.len(){
        //     c_g.push(pk_lag_basis[i]*c_evaluations[i]);
        // }
        // pk.product_domain.fft_in_place(&mut c_g);
        // let mut ghat = Vec::new();
        // for i in 0..c_evaluations.len()/2{
        //     ghat.push(c_g[i].clone().to_affine());
        // }
        let precompute_start = Instant::now();
        let ghat = self.precompute(epoch_challenge).unwrap();
        let precompute_duration = precompute_start.elapsed();
        println!("Time elapsed in precompute() is: {:?}", precompute_duration);
        println!("precompute: {:?}", ghat);

        let miner_start: Instant = Instant::now();
        let polynomial: DensePolynomial<_> = Self::prover_polynomial(epoch_challenge, address, nonce).unwrap();
        // let polynomial = epoch_challenge.epoch_polynomial().clone();
        let bases = ghat.clone();
        // let bases = self.precompute(epoch_challenge);

        let scalars = polynomial.coeffs;
        // println!("poly f scalar {:?}", scalars);
        let scalars = scalars.iter().map(|s| s.to_bigint()).collect::<Vec<_>>();

        let mut commitment = VariableBase::msm(&bases, &scalars);
        println!("commitment2 {:?}", commitment.to_affine());
        let (random_commit, _rand) = KZG10::generate_random_commit(&pk.lagrange_basis(), None, None)?;
        commitment.add_assign_mixed(&random_commit);
        let miner_duration = miner_start.elapsed();
        println!("Time elapsed in compute() is: {:?}", miner_duration);



        let commitment = KZGCommitment(commitment.into());

        let partial_solution = PartialSolution::new(address, nonce, commitment);
        // Check that the minimum target is met.
        if let Some(minimum_target) = minimum_proof_target {
            let proof_target = partial_solution.to_target()?;
            ensure!(
                proof_target >= minimum_target,
                "Prover solution was below the necessary proof target ({proof_target} < {minimum_target})"
            );
        }

        Ok((epoch_challenge.epoch_number(), partial_solution))
    }

    /// Returns a coinbase solution for the given epoch challenge and prover solutions.
    ///
    /// # Note
    /// This method does *not* check that the prover solutions are valid.
    pub fn check_solutions(
        &self,
        solutions: &CoinbaseSolution<N>,
        epoch_challenge: &EpochChallenge<N>,
        proof_target: u64,
    ) -> Result<()> {
        let timer = timer!("CoinbasePuzzle::verify");

        // Ensure the solutions are not empty.
        ensure!(!solutions.is_empty(), "There are no solutions to verify for the coinbase puzzle");

        // Ensure the number of partial solutions does not exceed `MAX_PROVER_SOLUTIONS`.
        if solutions.len() > N::MAX_SOLUTIONS {
            bail!(
                "The solutions exceed the allowed number of partial solutions. ({} > {})",
                solutions.len(),
                N::MAX_SOLUTIONS
            );
        }

        // Ensure the puzzle commitments are unique.
        if has_duplicates(solutions.puzzle_commitments()) {
            bail!("The solutions contain duplicate puzzle commitments");
        }
        lap!(timer, "Perform initial checks");

        // Verify each prover solution.
        if !cfg_iter!(solutions).all(|(_, solution)| {
            solution.verify(self.coinbase_verifying_key(), epoch_challenge, proof_target).unwrap_or(false)
        }) {
            bail!("The solutions contain an invalid prover solution");
        }
        finish!(timer, "Verify each solution");

        Ok(())
    }

    /// Returns the coinbase proving key.
    pub fn coinbase_proving_key(&self) -> Result<&CoinbaseProvingKey<N>> {
        match self {
            Self::Prover(coinbase_proving_key) => Ok(coinbase_proving_key),
            Self::Verifier(_) => bail!("Cannot fetch the coinbase proving key with a verifier"),
        }
    }

    /// Returns the coinbase verifying key.
    pub fn coinbase_verifying_key(&self) -> &CoinbaseVerifyingKey<N> {
        match self {
            Self::Prover(coinbase_proving_key) => &coinbase_proving_key.verifying_key,
            Self::Verifier(coinbase_verifying_key) => coinbase_verifying_key,
        }
    }
}

impl<N: Network> CoinbasePuzzle<N> {
    /// Checks that the degree for the epoch and prover polynomial is within bounds,
    /// and returns the evaluation domain for the product polynomial.
    pub(crate) fn product_domain(degree: u32) -> Result<EvaluationDomain<N::Field>> {
        ensure!(degree != 0, "Degree cannot be zero");
        let num_coefficients = degree.checked_add(1).ok_or_else(|| anyhow!("Degree is too large"))?;
        let product_num_coefficients = num_coefficients
            .checked_mul(2)
            .and_then(|t| t.checked_sub(1))
            .ok_or_else(|| anyhow!("Degree is too large"))?;
        assert_eq!(product_num_coefficients, 2 * degree + 1);
        let product_domain =
            EvaluationDomain::new(product_num_coefficients.try_into()?).ok_or_else(|| anyhow!("Invalid degree"))?;
        assert_eq!(product_domain.size(), (product_num_coefficients as usize).checked_next_power_of_two().unwrap());
        Ok(product_domain)
    }

    /// Returns the prover polynomial for the coinbase puzzle.
    fn prover_polynomial(
        epoch_challenge: &EpochChallenge<N>,
        address: Address<N>,
        nonce: u64,
    ) -> Result<DensePolynomial<<N::PairingCurve as PairingEngine>::Fr>> {
        let input = {
            let mut bytes = [0u8; 76];
            epoch_challenge.epoch_number().write_le(&mut bytes[..4])?;
            epoch_challenge.epoch_block_hash().write_le(&mut bytes[4..36])?;
            address.write_le(&mut bytes[36..68])?;
            nonce.write_le(&mut bytes[68..])?;

            bytes
        };

        // for i in 68..76 {
        //     print!("{:02x}", input[i]);
        // }
        // let len: u32 = epoch_challenge.epoch_polynomial().coeffs().len() as u32;
        // let len_bytes = len.to_bytes_le().unwrap();
        // for i in 0..4 {
        //     print!("{:02x}", len_bytes[i]);
        // }

        // for i in 36..68 {
        //     print!("{:02x}", input[i]);
        // }

        // for i in 4..36 {
        //     print!("{:02x}", input[i]);
        // }

        // for i in 0..4 {
        //     print!("{:02x}", input[i]);
        // }

        // print!("{:02x}", input[8]);
        // println!();

        // let mut work_fd = std::fs::File::create(format!("work.txt")).expect("create failed");
        // for i in 0..4 {
        //     write!(&work_fd, "{:02x}", input[i])?;
        // }
        // write!(&work_fd, ", ")?;

        // for i in 4..36 {
        //     write!(&work_fd, "{:02x}", input[i])?;
        // }
        // write!(&work_fd, ", ");

        // for i in 36..68 {
        //     write!(&work_fd, "{:02x}", input[i])?;
        // }
        // write!(&work_fd, ", ")?;

        // let len: u32 = epoch_challenge.epoch_polynomial().coeffs().len() as u32;
        // let len_bytes = len.to_bytes_le()?;
        // for i in 0..4 {
        //     write!(&work_fd, "{:02x}", len_bytes[i])?;
        // }
        // write!(&work_fd, ", ")?;

        // for i in 68..76 {
        //     write!(&work_fd, "{:02x}", input[i])?;
        // }

        Ok(hash_to_polynomial::<<N::PairingCurve as PairingEngine>::Fr>(&input, epoch_challenge.degree()))
    }
}


#[test]
fn test_point_to_string(){
    use rand::Rng;

    let mut rng = snarkvm_utilities::TestRng::default();

    let mut degree = 1 << 5;
    let ghat: Vec<snarkvm_curves::templates::twisted_edwards_extended::Affine<EdwardsParameters384>> =
        (0..degree).map(|_| rng.gen()).collect();

    for pp in ghat.iter(){
        let xx = pp.x.to_string();
        println!("{}", xx);
        // let yy = pp.y.to_string();
        // let zz = pp.y.to_string();

        let xxx = format!("{:x}", pp.x.to_bigint().to_biguint());
        println!("{}", xxx);
        assert_eq!(xx, xxx);
    }
}

#[test]
fn test_point_from_string(){

    use std::str::FromStr;
    use snarkvm_fields::PrimeField;
    let str = "ffff";
    let xx: snarkvm_fields::Fp384<snarkvm_curves::edwards_bls12::FqParameters384> = snarkvm_curves::edwards_bls12::Fq384::from_str(str).unwrap();
    let yy: snarkvm_fields::Fp384<snarkvm_curves::edwards_bls12::FqParameters384> = snarkvm_curves::edwards_bls12::Fq384::from_str(str).unwrap();

    let point = snarkvm_curves::templates::twisted_edwards_extended::Affine::<EdwardsParameters384>::new(xx, yy, xx*yy);

    println!("{:?}", point);

}