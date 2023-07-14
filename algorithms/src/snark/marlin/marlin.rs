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

use super::Certificate;
use crate::{
    fft::EvaluationDomain,
    polycommit::sonic_pc::{
        Commitment,
        CommitterUnionKey,
        Evaluations,
        LabeledCommitment,
        QuerySet,
        Randomness,
        SonicKZG10,
    },
    r1cs::ConstraintSynthesizer,
    snark::marlin::{
        ahp::{AHPError, AHPForR1CS, CircuitId, EvaluationsProvider},
        proof,
        prover,
        witness_label,
        CircuitProvingKey,
        CircuitVerifyingKey,
        MarlinMode,
        Proof,
        UniversalSRS,
    },
    srs::UniversalVerifier,
    AlgebraicSponge,
    SNARKError,
    SNARK,
};
use snarkvm_curves::PairingEngine;
use snarkvm_fields::{One, PrimeField, ToConstraintField, Zero};
use snarkvm_utilities::{to_bytes_le, ToBytes};

use anyhow::{anyhow, Result};
use core::marker::PhantomData;
use itertools::Itertools;
use rand::{CryptoRng, Rng};
use std::{borrow::Borrow, collections::BTreeMap, ops::Deref, sync::Arc};

use crate::srs::UniversalProver;
#[cfg(not(feature = "std"))]
use snarkvm_utilities::println;

/// The Marlin proof system.
#[derive(Clone, Debug)]
pub struct MarlinSNARK<E: PairingEngine, FS: AlgebraicSponge<E::Fq, 2>, MM: MarlinMode>(
    #[doc(hidden)] PhantomData<(E, FS, MM)>,
);

impl<E: PairingEngine, FS: AlgebraicSponge<E::Fq, 2>, MM: MarlinMode> MarlinSNARK<E, FS, MM> {
    /// The personalization string for this protocol.
    /// Used to personalize the Fiat-Shamir RNG.
    pub const PROTOCOL_NAME: &'static [u8] = b"MARLIN-2019";

    // TODO: implement optimizations resulting from batching
    //       (e.g. computing a common set of Lagrange powers, FFT precomputations, etc)
    pub fn batch_circuit_setup<C: ConstraintSynthesizer<E::Fr>>(
        universal_srs: &UniversalSRS<E>,
        circuits: &[&C],
    ) -> Result<Vec<(CircuitProvingKey<E, MM>, CircuitVerifyingKey<E>)>> {
        let index_time = start_timer!(|| "Marlin::CircuitSetup");

        let universal_prover = &universal_srs.to_universal_prover()?;

        let mut circuit_keys = Vec::with_capacity(circuits.len());
        for circuit in circuits {
            let indexed_circuit = AHPForR1CS::<_, MM>::index(*circuit)?;
            // TODO: Add check that c is in the correct mode.
            // Ensure the universal SRS supports the circuit size.
            universal_srs
                .download_powers_for(0..indexed_circuit.max_degree())
                .map_err(|e| anyhow!("Failed to download powers for degree {}: {e}", indexed_circuit.max_degree()))?;
            let coefficient_support = AHPForR1CS::<E::Fr, MM>::get_degree_bounds(&indexed_circuit.index_info);

            // Marlin only needs degree 2 random polynomials.
            let supported_hiding_bound = 1;
            let (committer_key, _) = SonicKZG10::<E, FS>::trim(
                universal_srs,
                indexed_circuit.max_degree(),
                [indexed_circuit.constraint_domain_size()],
                supported_hiding_bound,
                Some(coefficient_support.as_slice()),
            )?;

            let ck = CommitterUnionKey::union(std::iter::once(&committer_key));

            let commit_time = start_timer!(|| format!("Commit to index polynomials for {}", indexed_circuit.id));
            let (mut circuit_commitments, circuit_commitment_randomness): (_, _) =
                SonicKZG10::<E, FS>::commit(universal_prover, &ck, indexed_circuit.iter().map(Into::into), None)?;
            end_timer!(commit_time);

            circuit_commitments.sort_by(|c1, c2| c1.label().cmp(c2.label()));
            let circuit_commitments = circuit_commitments.into_iter().map(|c| *c.commitment()).collect();
            let circuit_verifying_key = CircuitVerifyingKey {
                circuit_info: indexed_circuit.index_info,
                circuit_commitments,
                id: indexed_circuit.id,
            };
            let circuit_proving_key = CircuitProvingKey {
                circuit: Arc::new(indexed_circuit),
                circuit_commitment_randomness,
                circuit_verifying_key: circuit_verifying_key.clone(),
                committer_key: Arc::new(committer_key),
            };
            circuit_keys.push((circuit_proving_key, circuit_verifying_key));
        }

        end_timer!(index_time);
        Ok(circuit_keys)
    }

    fn init_sponge<'a>(
        fs_parameters: &FS::Parameters,
        inputs_and_batch_sizes: &BTreeMap<CircuitId, (usize, &[Vec<E::Fr>])>,
        circuit_commitments: impl Iterator<Item = &'a [crate::polycommit::sonic_pc::Commitment<E>]>,
    ) -> FS {
        let mut sponge = FS::new_with_parameters(fs_parameters);
        sponge.absorb_bytes(&to_bytes_le![&Self::PROTOCOL_NAME].unwrap());
        for (batch_size, inputs) in inputs_and_batch_sizes.values() {
            sponge.absorb_bytes(&(u64::try_from(*batch_size).unwrap()).to_le_bytes());
            for input in inputs.iter() {
                sponge.absorb_nonnative_field_elements(input.iter().copied());
            }
        }
        for circuit_specific_commitments in circuit_commitments {
            sponge.absorb_native_field_elements(circuit_specific_commitments);
        }
        sponge
    }

    fn init_sponge_for_certificate(
        fs_parameters: &FS::Parameters,
        circuit_commitments: &[crate::polycommit::sonic_pc::Commitment<E>],
    ) -> FS {
        let mut sponge = FS::new_with_parameters(fs_parameters);
        sponge.absorb_bytes(&to_bytes_le![&Self::PROTOCOL_NAME].unwrap());
        sponge.absorb_native_field_elements(circuit_commitments);
        sponge
    }

    fn absorb_labeled_with_msg(
        comms: &[LabeledCommitment<Commitment<E>>],
        message: &prover::ThirdMessage<E::Fr>,
        sponge: &mut FS,
    ) {
        let commitments: Vec<_> = comms.iter().map(|c| *c.commitment()).collect();
        Self::absorb_with_msg(&commitments, message, sponge)
    }

    fn absorb_labeled(comms: &[LabeledCommitment<Commitment<E>>], sponge: &mut FS) {
        let commitments: Vec<_> = comms.iter().map(|c| *c.commitment()).collect();
        Self::absorb(&commitments, sponge);
    }

    fn absorb(commitments: &[Commitment<E>], sponge: &mut FS) {
        let sponge_time = start_timer!(|| "Absorbing commitments");
        sponge.absorb_native_field_elements(commitments);
        end_timer!(sponge_time);
    }

    fn absorb_with_msg(commitments: &[Commitment<E>], msg: &prover::ThirdMessage<E::Fr>, sponge: &mut FS) {
        let sponge_time = start_timer!(|| "Absorbing commitments and message");
        Self::absorb(commitments, sponge);
        for sum in msg.sums.iter() {
            sponge.absorb_nonnative_field_elements([sum.sum_a, sum.sum_b, sum.sum_c]);
        }
        end_timer!(sponge_time);
    }
}

impl<E: PairingEngine, FS, MM> SNARK for MarlinSNARK<E, FS, MM>
where
    E::Fr: PrimeField,
    E::Fq: PrimeField,
    FS: AlgebraicSponge<E::Fq, 2>,
    MM: MarlinMode,
{
    type BaseField = E::Fq;
    type Certificate = Certificate<E>;
    type FSParameters = FS::Parameters;
    type FiatShamirRng = FS;
    type Proof = Proof<E>;
    type ProvingKey = CircuitProvingKey<E, MM>;
    type ScalarField = E::Fr;
    type UniversalProver = UniversalProver<E>;
    type UniversalSRS = UniversalSRS<E>;
    type UniversalVerifier = UniversalVerifier<E>;
    type VerifierInput = [E::Fr];
    type VerifyingKey = CircuitVerifyingKey<E>;

    fn universal_setup(max_degree: usize) -> Result<Self::UniversalSRS, SNARKError> {
        let setup_time = start_timer!(|| { format!("Marlin::UniversalSetup with max_degree {max_degree}",) });
        let srs = SonicKZG10::<E, FS>::load_srs(max_degree).map_err(Into::into);
        end_timer!(setup_time);
        srs
    }

    /// Generates the circuit proving and verifying keys.
    /// This is a deterministic algorithm that anyone can rerun.
    fn circuit_setup<C: ConstraintSynthesizer<E::Fr>>(
        universal_srs: &Self::UniversalSRS,
        circuit: &C,
    ) -> Result<(Self::ProvingKey, Self::VerifyingKey)> {
        let mut circuit_keys = Self::batch_circuit_setup(universal_srs, &[circuit])?;
        assert_eq!(circuit_keys.len(), 1);
        Ok(circuit_keys.pop().unwrap())
    }

    /// Prove that the verifying key indeed includes a part of the reference string,
    /// as well as the indexed circuit (i.e. the circuit as a set of linear-sized polynomials).
    fn prove_vk(
        universal_prover: &Self::UniversalProver,
        fs_parameters: &Self::FSParameters,
        verifying_key: &Self::VerifyingKey,
        proving_key: &Self::ProvingKey,
    ) -> Result<Self::Certificate, SNARKError> {
        // Initialize sponge
        let mut sponge = Self::init_sponge_for_certificate(fs_parameters, &verifying_key.circuit_commitments);
        // Compute challenges for linear combination, and the point to evaluate the polynomials at.
        // The linear combination requires `num_polynomials - 1` coefficients
        // (since the first coeff is 1), and so we squeeze out `num_polynomials` points.
        let mut challenges = sponge.squeeze_nonnative_field_elements(verifying_key.circuit_commitments.len());
        let point = challenges.pop().unwrap();
        let one = E::Fr::one();
        let linear_combination_challenges = core::iter::once(&one).chain(challenges.iter());

        // We will construct a linear combination and provide a proof of evaluation of the lc at `point`.
        let mut lc = crate::polycommit::sonic_pc::LinearCombination::empty("circuit_check");
        for (poly, &c) in proving_key.circuit.iter().zip(linear_combination_challenges) {
            lc.add(c, poly.label());
        }

        let circuit_id = std::iter::once(&verifying_key.id);
        let query_set = QuerySet::from_iter([("circuit_check".into(), ("challenge".into(), point))]);
        let commitments = verifying_key
            .iter()
            .cloned()
            .zip_eq(AHPForR1CS::<E::Fr, MM>::index_polynomial_info(circuit_id).values())
            .map(|(c, info)| LabeledCommitment::new_with_info(info, c))
            .collect::<Vec<_>>();

        let committer_key = CommitterUnionKey::union(std::iter::once(proving_key.committer_key.as_ref()));

        let certificate = SonicKZG10::<E, FS>::open_combinations(
            universal_prover,
            &committer_key,
            &[lc],
            proving_key.circuit.iter(),
            &commitments,
            &query_set,
            &proving_key.circuit_commitment_randomness.clone(),
            &mut sponge,
        )?;

        Ok(Self::Certificate::new(certificate))
    }

    /// Verify that the verifying key indeed includes a part of the reference string,
    /// as well as the indexed circuit (i.e. the circuit as a set of linear-sized polynomials).
    fn verify_vk<C: ConstraintSynthesizer<Self::ScalarField>>(
        universal_verifier: &Self::UniversalVerifier,
        fs_parameters: &Self::FSParameters,
        circuit: &C,
        verifying_key: &Self::VerifyingKey,
        certificate: &Self::Certificate,
    ) -> Result<bool, SNARKError> {
        let circuit_id = &verifying_key.id;
        let info = AHPForR1CS::<E::Fr, MM>::index_polynomial_info(std::iter::once(circuit_id));
        // Initialize sponge.
        let mut sponge = Self::init_sponge_for_certificate(fs_parameters, &verifying_key.circuit_commitments);
        // Compute challenges for linear combination, and the point to evaluate the polynomials at.
        // The linear combination requires `num_polynomials - 1` coefficients
        // (since the first coeff is 1), and so we squeeze out `num_polynomials` points.
        let mut challenges = sponge.squeeze_nonnative_field_elements(verifying_key.circuit_commitments.len());
        let point = challenges.pop().unwrap();

        let evaluations_at_point = AHPForR1CS::<E::Fr, MM>::evaluate_index_polynomials(circuit, circuit_id, point)?;
        let one = E::Fr::one();
        let linear_combination_challenges = core::iter::once(&one).chain(challenges.iter());

        // We will construct a linear combination and provide a proof of evaluation of the lc at `point`.
        let mut lc = crate::polycommit::sonic_pc::LinearCombination::empty("circuit_check");
        let mut evaluation = E::Fr::zero();
        for ((label, &c), eval) in info.keys().zip_eq(linear_combination_challenges).zip_eq(evaluations_at_point) {
            lc.add(c, label.as_str());
            evaluation += c * eval;
        }

        let query_set = QuerySet::from_iter([("circuit_check".into(), ("challenge".into(), point))]);
        let commitments = verifying_key
            .iter()
            .cloned()
            .zip_eq(info.values())
            .map(|(c, info)| LabeledCommitment::new_with_info(info, c))
            .collect::<Vec<_>>();
        let evaluations = Evaluations::from_iter([(("circuit_check".into(), point), evaluation)]);

        SonicKZG10::<E, FS>::check_combinations(
            universal_verifier,
            &[lc],
            &commitments,
            &query_set,
            &evaluations,
            &certificate.pc_proof,
            &mut sponge,
        )
        .map_err(Into::into)
    }

    #[allow(clippy::only_used_in_recursion)]
    /// This is the main entrypoint for creating proofs.
    /// You can find a specification of the prover algorithm in:
    /// https://github.com/AleoHQ/protocol-docs/tree/main/marlin
    fn prove_batch<C: ConstraintSynthesizer<E::Fr>, R: Rng + CryptoRng>(
        universal_prover: &Self::UniversalProver,
        fs_parameters: &Self::FSParameters,
        keys_to_constraints: &BTreeMap<&CircuitProvingKey<E, MM>, &[C]>,
        zk_rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        let prover_time = start_timer!(|| "Marlin::Prover");
        if keys_to_constraints.is_empty() {
            return Err(SNARKError::EmptyBatch);
        }

        let mut circuits_to_constraints = BTreeMap::new();
        for (pk, constraints) in keys_to_constraints {
            circuits_to_constraints.insert(pk.circuit.deref(), *constraints);
        }
        let prover_state = AHPForR1CS::<_, MM>::init_prover(&circuits_to_constraints)?;

        // extract information from the prover key and state to consume in further calculations
        let mut batch_sizes = BTreeMap::new();
        let mut circuit_infos = BTreeMap::new();
        let mut inputs_and_batch_sizes = BTreeMap::new();
        let mut total_instances = 0;
        let mut public_inputs = BTreeMap::new(); // inputs need to live longer than the rest of prover_state
        let mut circuit_ids = Vec::with_capacity(keys_to_constraints.len());
        for pk in keys_to_constraints.keys() {
            let batch_size = prover_state.batch_size(&pk.circuit).ok_or(SNARKError::CircuitNotFound)?;
            let public_input = prover_state.public_inputs(&pk.circuit).ok_or(SNARKError::CircuitNotFound)?;
            let padded_public_input =
                prover_state.padded_public_inputs(&pk.circuit).ok_or(SNARKError::CircuitNotFound)?;
            let circuit_id = pk.circuit.id;
            batch_sizes.insert(circuit_id, batch_size);
            circuit_infos.insert(circuit_id, &pk.circuit_verifying_key.circuit_info);
            inputs_and_batch_sizes.insert(circuit_id, (batch_size, padded_public_input));
            total_instances += batch_size;
            public_inputs.insert(circuit_id, public_input);
            circuit_ids.push(circuit_id);
        }
        assert_eq!(prover_state.total_instances, total_instances);

        let committer_key = CommitterUnionKey::union(keys_to_constraints.keys().map(|pk| pk.committer_key.deref()));

        let circuit_commitments =
            keys_to_constraints.keys().map(|pk| pk.circuit_verifying_key.circuit_commitments.as_slice());

        let mut sponge = Self::init_sponge(fs_parameters, &inputs_and_batch_sizes, circuit_commitments.clone());

        // --------------------------------------------------------------------
        // First round

        let mut prover_state = AHPForR1CS::<_, MM>::prover_first_round(prover_state, zk_rng)?;

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_commitments, first_commitment_randomnesses) = {
            let first_round_oracles = Arc::get_mut(prover_state.first_round_oracles.as_mut().unwrap()).unwrap();
            SonicKZG10::<E, FS>::commit(
                universal_prover,
                &committer_key,
                first_round_oracles.iter_for_commit(),
                Some(zk_rng),
            )?
        };
        end_timer!(first_round_comm_time);

        Self::absorb_labeled(&first_commitments, &mut sponge);

        let (verifier_first_message, verifier_state) = AHPForR1CS::<_, MM>::verifier_first_round(
            &batch_sizes,
            &circuit_infos,
            prover_state.max_constraint_domain,
            prover_state.max_non_zero_domain,
            &mut sponge,
        )?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        let (second_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_second_round(&verifier_first_message, prover_state, zk_rng);

        let second_round_comm_time = start_timer!(|| "Committing to second round polys");
        let (second_commitments, second_commitment_randomnesses) = SonicKZG10::<E, FS>::commit(
            universal_prover,
            &committer_key,
            second_oracles.iter().map(Into::into),
            Some(zk_rng),
        )?;
        end_timer!(second_round_comm_time);

        Self::absorb_labeled(&second_commitments, &mut sponge);

        let (verifier_second_msg, verifier_state) =
            AHPForR1CS::<_, MM>::verifier_second_round(verifier_state, &mut sponge)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round

        let (prover_third_message, third_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_third_round(&verifier_second_msg, prover_state, zk_rng)?;

        let third_round_comm_time = start_timer!(|| "Committing to third round polys");
        let (third_commitments, third_commitment_randomnesses) = SonicKZG10::<E, FS>::commit(
            universal_prover,
            &committer_key,
            third_oracles.iter().map(Into::into),
            Some(zk_rng),
        )?;
        end_timer!(third_round_comm_time);

        Self::absorb_labeled_with_msg(&third_commitments, &prover_third_message, &mut sponge);

        let (verifier_third_msg, verifier_state) =
            AHPForR1CS::<_, MM>::verifier_third_round(verifier_state, &mut sponge)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Fourth round

        let first_round_oracles = Arc::clone(prover_state.first_round_oracles.as_ref().unwrap());
        let fourth_oracles = AHPForR1CS::<_, MM>::prover_fourth_round(verifier_third_msg, prover_state, zk_rng)?;

        let fourth_round_comm_time = start_timer!(|| "Committing to fourth round polys");
        let (fourth_commitments, fourth_commitment_randomnesses) = SonicKZG10::<E, FS>::commit(
            universal_prover,
            &committer_key,
            fourth_oracles.iter().map(Into::into),
            Some(zk_rng),
        )?;
        end_timer!(fourth_round_comm_time);

        Self::absorb_labeled(&fourth_commitments, &mut sponge);

        let verifier_state = AHPForR1CS::<_, MM>::verifier_fourth_round(verifier_state, &mut sponge)?;
        // --------------------------------------------------------------------

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = keys_to_constraints
            .keys()
            .flat_map(|pk| pk.circuit.iter())
            .chain(first_round_oracles.iter_for_open())
            .chain(second_oracles.iter())
            .chain(third_oracles.iter())
            .chain(fourth_oracles.iter())
            .collect();
        assert!(
            polynomials.len()
                == keys_to_constraints.len() * 12 + // polys for row, col, rowcol, val
            AHPForR1CS::<E::Fr, MM>::num_first_round_oracles(total_instances) +
            AHPForR1CS::<E::Fr, MM>::num_second_round_oracles() +
            AHPForR1CS::<E::Fr, MM>::num_third_round_oracles(keys_to_constraints.len()) +
            AHPForR1CS::<E::Fr, MM>::num_fourth_round_oracles()
        );

        // Gather commitments in one vector.
        let witness_commitments = first_commitments.chunks_exact(3);
        let mask_poly = MM::ZK.then(|| *witness_commitments.remainder()[0].commitment());
        let witness_commitments = witness_commitments
            .map(|c| proof::WitnessCommitments {
                w: *c[0].commitment(),
                z_a: *c[1].commitment(),
                z_b: *c[2].commitment(),
            })
            .collect();
        let third_commitments_chunked = third_commitments.chunks_exact(3);

        #[rustfmt::skip]
        let commitments = proof::Commitments {
            witness_commitments,
            mask_poly,

            g_1: *second_commitments[0].commitment(),
            h_1: *second_commitments[1].commitment(),

            g_a_commitments: third_commitments_chunked.clone().map(|c| *c[0].commitment()).collect(),
            g_b_commitments: third_commitments_chunked.clone().map(|c| *c[1].commitment()).collect(),
            g_c_commitments: third_commitments_chunked.map(|c| *c[2].commitment()).collect(),

            h_2: *fourth_commitments[0].commitment(),
        };

        let labeled_commitments: Vec<_> = circuit_commitments
            .into_iter()
            .flatten()
            .zip_eq(AHPForR1CS::<E::Fr, MM>::index_polynomial_info(circuit_ids.iter()).values())
            .map(|(c, info)| LabeledCommitment::new_with_info(info, *c))
            .chain(first_commitments.into_iter())
            .chain(second_commitments.into_iter())
            .chain(third_commitments.into_iter())
            .chain(fourth_commitments.into_iter())
            .collect();

        // Gather commitment randomness together.
        let commitment_randomnesses: Vec<Randomness<E>> = keys_to_constraints
            .keys()
            .flat_map(|pk| pk.circuit_commitment_randomness.clone())
            .chain(first_commitment_randomnesses)
            .chain(second_commitment_randomnesses)
            .chain(third_commitment_randomnesses)
            .chain(fourth_commitment_randomnesses)
            .collect();

        if !MM::ZK {
            let empty_randomness = Randomness::<E>::empty();
            assert!(commitment_randomnesses.iter().all(|r| r == &empty_randomness));
        }

        // Compute the AHP verifier's query set.
        let (query_set, verifier_state) = AHPForR1CS::<_, MM>::verifier_query_set(verifier_state);
        let lc_s = AHPForR1CS::<_, MM>::construct_linear_combinations(
            &public_inputs,
            &polynomials,
            &prover_third_message,
            &verifier_state,
        )?;

        let eval_time = start_timer!(|| "Evaluating linear combinations over query set");
        let mut evaluations = std::collections::BTreeMap::new();
        for (label, (_, point)) in query_set.to_set() {
            if !AHPForR1CS::<E::Fr, MM>::LC_WITH_ZERO_EVAL.contains(&label.as_str()) {
                let lc = lc_s.get(&label).ok_or_else(|| AHPError::MissingEval(label.to_string()))?;
                let evaluation = polynomials.get_lc_eval(lc, point)?;
                evaluations.insert(label, evaluation);
            }
        }

        let evaluations = proof::Evaluations::from_map(&evaluations, batch_sizes.clone());
        end_timer!(eval_time);

        sponge.absorb_nonnative_field_elements(evaluations.to_field_elements());

        let pc_proof = SonicKZG10::<E, FS>::open_combinations(
            universal_prover,
            &committer_key,
            lc_s.values(),
            polynomials,
            &labeled_commitments,
            &query_set.to_set(),
            &commitment_randomnesses,
            &mut sponge,
        )?;

        let proof = Proof::<E>::new(batch_sizes, commitments, evaluations, prover_third_message, pc_proof)?;
        assert_eq!(proof.pc_proof.is_hiding(), MM::ZK);

        end_timer!(prover_time);
        Ok(proof)
    }

    /// This is the main entrypoint for verifying proofs.
    /// You can find a specification of the verifier algorithm in:
    /// https://github.com/AleoHQ/protocol-docs/tree/main/marlin
    fn verify_batch<B: Borrow<Self::VerifierInput>>(
        universal_verifier: &Self::UniversalVerifier,
        fs_parameters: &Self::FSParameters,
        keys_to_inputs: &BTreeMap<&Self::VerifyingKey, &[B]>,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        if keys_to_inputs.is_empty() {
            return Err(SNARKError::EmptyBatch);
        }

        let batch_sizes_vec = proof.batch_sizes()?;
        let mut batch_sizes = BTreeMap::new();
        for (i, (vk, public_inputs_i)) in keys_to_inputs.iter().enumerate() {
            batch_sizes.insert(vk.id, batch_sizes_vec[i]);

            if public_inputs_i.is_empty() {
                return Err(SNARKError::EmptyBatch);
            }

            if public_inputs_i.len() != batch_sizes_vec[i] {
                return Err(SNARKError::BatchSizeMismatch);
            }
        }

        // collect values into structures for our calculations
        let mut max_constraint_domain = None;
        let mut max_non_zero_domain = None;
        let mut public_inputs = BTreeMap::new();
        let mut padded_public_vec = Vec::with_capacity(keys_to_inputs.len());
        let mut inputs_and_batch_sizes = BTreeMap::new();
        let mut input_domains = BTreeMap::new();
        let mut circuit_infos = BTreeMap::new();
        let mut circuit_ids = Vec::with_capacity(keys_to_inputs.len());
        for (vk, public_inputs_i) in keys_to_inputs.iter() {
            let constraint_domains =
                AHPForR1CS::<_, MM>::max_constraint_domain(&vk.circuit_info, max_constraint_domain)?;
            max_constraint_domain = constraint_domains.max_constraint_domain;
            let non_zero_domains = AHPForR1CS::<_, MM>::max_non_zero_domain(&vk.circuit_info, max_non_zero_domain)?;
            max_non_zero_domain = non_zero_domains.max_non_zero_domain;

            let input_domain = EvaluationDomain::<E::Fr>::new(vk.circuit_info.num_public_inputs).unwrap();
            input_domains.insert(vk.id, input_domain);

            let (padded_public_inputs_i, parsed_public_inputs_i): (Vec<_>, Vec<_>) = {
                public_inputs_i
                    .iter()
                    .map(|input| {
                        let input = input.borrow().to_field_elements().unwrap();
                        let mut new_input = vec![E::Fr::one()];
                        new_input.extend_from_slice(&input);
                        new_input.resize(input.len().max(input_domain.size()), E::Fr::zero());
                        if cfg!(debug_assertions) {
                            println!("Number of padded public variables: {}", new_input.len());
                        }
                        let unformatted = prover::ConstraintSystem::unformat_public_input(&new_input);
                        (new_input, unformatted)
                    })
                    .unzip()
            };
            let circuit_id = vk.id;
            public_inputs.insert(circuit_id, parsed_public_inputs_i);
            padded_public_vec.push(padded_public_inputs_i);
            circuit_infos.insert(circuit_id, &vk.circuit_info);
            circuit_ids.push(circuit_id);
        }
        for (i, (vk, &batch_size)) in keys_to_inputs.keys().zip(batch_sizes.values()).enumerate() {
            inputs_and_batch_sizes.insert(vk.id, (batch_size, padded_public_vec[i].as_slice()));
        }

        let comms = &proof.commitments;
        let proof_has_correct_zk_mode = if MM::ZK {
            proof.pc_proof.is_hiding() & comms.mask_poly.is_some()
        } else {
            !proof.pc_proof.is_hiding() & comms.mask_poly.is_none()
        };
        if !proof_has_correct_zk_mode {
            eprintln!(
                "Found `mask_poly` in the first round when not expected, or proof has incorrect hiding mode ({})",
                proof.pc_proof.is_hiding()
            );
            return Ok(false);
        }

        let verifier_time = start_timer!(|| format!("Marlin::Verify with batch sizes: {:?}", batch_sizes));

        let first_round_info = AHPForR1CS::<E::Fr, MM>::first_round_polynomial_info(batch_sizes.iter());

        let mut first_comms_consumed = 0;
        let mut first_commitments = batch_sizes
            .iter()
            .flat_map(|(&circuit_id, &batch_size)| {
                let first_comms = comms.witness_commitments[first_comms_consumed..][..batch_size]
                    .iter()
                    .enumerate()
                    .flat_map(|(j, w_comm)| {
                        [
                            LabeledCommitment::new_with_info(
                                &first_round_info[&witness_label(circuit_id, "w", j)],
                                w_comm.w,
                            ),
                            LabeledCommitment::new_with_info(
                                &first_round_info[&witness_label(circuit_id, "z_a", j)],
                                w_comm.z_a,
                            ),
                            LabeledCommitment::new_with_info(
                                &first_round_info[&witness_label(circuit_id, "z_b", j)],
                                w_comm.z_b,
                            ),
                        ]
                    })
                    .collect_vec();
                first_comms_consumed += batch_size;
                first_comms
            })
            .collect_vec();

        if MM::ZK {
            first_commitments.push(LabeledCommitment::new_with_info(
                first_round_info.get("mask_poly").unwrap(),
                comms.mask_poly.unwrap(),
            ));
        }

        let second_round_info =
            AHPForR1CS::<E::Fr, MM>::second_round_polynomial_info(max_constraint_domain.unwrap().size());
        let second_commitments = [
            LabeledCommitment::new_with_info(&second_round_info["g_1"], comms.g_1),
            LabeledCommitment::new_with_info(&second_round_info["h_1"], comms.h_1),
        ];

        let third_round_info = AHPForR1CS::<E::Fr, MM>::third_round_polynomial_info(circuit_infos.clone().into_iter());
        let third_commitments = comms
            .g_a_commitments
            .iter()
            .zip_eq(comms.g_b_commitments.iter())
            .zip_eq(comms.g_c_commitments.iter())
            .zip_eq(circuit_ids.iter())
            .flat_map(|(((g_a, g_b), g_c), circuit_id)| {
                [
                    LabeledCommitment::new_with_info(&third_round_info[&witness_label(*circuit_id, "g_a", 0)], *g_a),
                    LabeledCommitment::new_with_info(&third_round_info[&witness_label(*circuit_id, "g_b", 0)], *g_b),
                    LabeledCommitment::new_with_info(&third_round_info[&witness_label(*circuit_id, "g_c", 0)], *g_c),
                ]
            })
            .collect_vec();

        let fourth_round_info = AHPForR1CS::<E::Fr, MM>::fourth_round_polynomial_info();
        let fourth_commitments = [LabeledCommitment::new_with_info(&fourth_round_info["h_2"], comms.h_2)];

        let circuit_commitments = keys_to_inputs.keys().map(|vk| vk.circuit_commitments.as_slice());
        let mut sponge = Self::init_sponge(fs_parameters, &inputs_and_batch_sizes, circuit_commitments.clone());

        // --------------------------------------------------------------------
        // First round
        let first_round_time = start_timer!(|| "First round");
        Self::absorb_labeled(&first_commitments, &mut sponge);
        let (_, verifier_state) = AHPForR1CS::<_, MM>::verifier_first_round(
            &batch_sizes,
            &circuit_infos,
            max_constraint_domain.unwrap(),
            max_non_zero_domain.unwrap(),
            &mut sponge,
        )?;
        end_timer!(first_round_time);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round
        let second_round_time = start_timer!(|| "Second round");
        Self::absorb_labeled(&second_commitments, &mut sponge);
        let (_, verifier_state) = AHPForR1CS::<_, MM>::verifier_second_round(verifier_state, &mut sponge)?;
        end_timer!(second_round_time);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round
        let third_round_time = start_timer!(|| "Third round");

        Self::absorb_labeled_with_msg(&third_commitments, &proof.msg, &mut sponge);
        let (_, verifier_state) = AHPForR1CS::<_, MM>::verifier_third_round(verifier_state, &mut sponge)?;
        end_timer!(third_round_time);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Fourth round
        let fourth_round_time = start_timer!(|| "Fourth round");

        Self::absorb_labeled(&fourth_commitments, &mut sponge);
        let verifier_state = AHPForR1CS::<_, MM>::verifier_fourth_round(verifier_state, &mut sponge)?;
        end_timer!(fourth_round_time);
        // --------------------------------------------------------------------

        // Collect degree bounds for commitments. Indexed polynomials have *no*
        // degree bounds because we know the committed index polynomial has the
        // correct degree.

        // Gather commitments in one vector.
        let commitments: Vec<_> = circuit_commitments
            .into_iter()
            .flatten()
            .zip_eq(AHPForR1CS::<E::Fr, MM>::index_polynomial_info(circuit_ids.iter()).values())
            .map(|(c, info)| LabeledCommitment::new_with_info(info, *c))
            .chain(first_commitments)
            .chain(second_commitments)
            .chain(third_commitments)
            .chain(fourth_commitments)
            .collect();

        let query_set_time = start_timer!(|| "Constructing query set");
        let (query_set, verifier_state) = AHPForR1CS::<_, MM>::verifier_query_set(verifier_state);
        end_timer!(query_set_time);

        sponge.absorb_nonnative_field_elements(proof.evaluations.to_field_elements());

        let mut evaluations = Evaluations::new();

        let mut current_circuit_id = "".to_string();
        let mut circuit_index: i64 = -1;
        for (label, (_point_name, q)) in query_set.to_set() {
            if AHPForR1CS::<E::Fr, MM>::LC_WITH_ZERO_EVAL.contains(&label.as_ref()) {
                evaluations.insert((label, q), E::Fr::zero());
            } else {
                if label != "g_1" {
                    let circuit_id = CircuitId::from_witness_label(&label).to_string();
                    if circuit_id != current_circuit_id {
                        circuit_index += 1;
                        current_circuit_id = circuit_id;
                    }
                }
                let eval = proof
                    .evaluations
                    .get(circuit_index as usize, &label)
                    .ok_or_else(|| AHPError::MissingEval(label.clone()))?;
                evaluations.insert((label, q), eval);
            }
        }

        let lc_time = start_timer!(|| "Constructing linear combinations");
        let lc_s = AHPForR1CS::<_, MM>::construct_linear_combinations(
            &public_inputs,
            &evaluations,
            &proof.msg,
            &verifier_state,
        )?;
        end_timer!(lc_time);

        let pc_time = start_timer!(|| "Checking linear combinations with PC");
        let evaluations_are_correct = SonicKZG10::<E, FS>::check_combinations(
            universal_verifier,
            lc_s.values(),
            &commitments,
            &query_set.to_set(),
            &evaluations,
            &proof.pc_proof,
            &mut sponge,
        )?;
        end_timer!(pc_time);

        if !evaluations_are_correct {
            #[cfg(debug_assertions)]
            eprintln!("SonicKZG10::Check failed");
        }
        end_timer!(verifier_time, || format!(
            " SonicKZG10::Check for AHP Verifier linear equations: {}",
            evaluations_are_correct & proof_has_correct_zk_mode
        ));
        Ok(evaluations_are_correct & proof_has_correct_zk_mode)
    }
}
