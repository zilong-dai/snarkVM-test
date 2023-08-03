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

use console::{account::Address, network::prelude::*};
use ledger_committee::Committee;

use indexmap::IndexMap;

/// A safety bound (sanity-check) for the coinbase reward.
pub const MAX_COINBASE_REWARD: u64 = 237_823_432; // Coinbase reward at block 1.

/// Returns the staking rewards for the given committee and block reward.
/// The staking reward is defined as: `block_reward * stake / total_stake`.
///
/// This method ensures that stakers who are bonded to validators with more than **25%**
/// of the total stake will not receive a staking reward. In addition, this method
/// ensures stakers who have less than 1 credit are not eligible for a staking reward.
///
/// The choice of 25% is to ensure at least 4 validators are operational at any given time,
/// since our security model adheres to 3f+1, where f=1. As such, we tolerate Byzantine behavior
/// up to 33% of the total stake.
pub fn staking_rewards<'a, N: Network>(
    stakers: IndexMap<Address<N>, (Address<N>, u64)>,
    committee: &Committee<N>,
    block_reward: u64,
) -> IndexMap<Address<N>, (Address<N>, u64)> {
    // If the list of stakers is empty or there is no stake, return an empty map.
    if stakers.len() == 0 || committee.total_stake() == 0 {
        return Default::default();
    }

    // Initialize a map to store the staking rewards.
    let mut next_stakers = IndexMap::with_capacity(stakers.len());

    // Calculate the rewards for the individual stakers.
    for (staker, (validator, stake)) in stakers {
        // If the validator has more than 25% of the total stake, skip the staker.
        if committee.get_stake(validator) > committee.total_stake().saturating_div(4) {
            trace!("Validator {validator} has more than 25% of the total stake - skipping {staker}");
            continue;
        }
        // If the staker has less than 1 credit, skip the staker.
        if stake < 1_000_000 {
            trace!("Staker has less than 1 credit - skipping {staker}");
            continue;
        }

        // Compute the numerator.
        let numerator = (block_reward as u128).saturating_mul(stake as u128);
        // Compute the denominator.
        // Note: We guarantee this denominator cannot be 0 (as we return early if the total stake is 0).
        let denominator = committee.total_stake() as u128;
        // Compute the quotient.
        let quotient = numerator.saturating_div(denominator);
        // Ensure the staking reward is within a safe bound.
        if quotient > MAX_COINBASE_REWARD as u128 {
            error!("Staking reward ({quotient}) is too large - skipping {staker}");
            continue;
        }
        // Cast the staking reward as a u64.
        // Note: This '.expect' is guaranteed to be safe, as we ensure the quotient is within a safe bound.
        let staking_reward = u64::try_from(quotient).expect("Staking reward is too large");
        // Add the staking reward to the map.
        next_stakers.insert(staker, (validator, stake.saturating_add(staking_reward)));
    }

    // Return the updated stakers.
    next_stakers
}

/// Returns the proving rewards for a given coinbase reward and list of prover solutions.
/// The prover reward is defined as: `puzzle_reward * (proof_target / combined_proof_target)`.
pub fn proving_rewards<N: Network>(
    proof_targets: Vec<(Address<N>, u128)>,
    puzzle_reward: u64,
    combined_proof_target: u128,
) -> IndexMap<Address<N>, u64> {
    // (Debug Mode) Ensure the combined proof target is equal to the sum of the proof targets.
    debug_assert_eq!(combined_proof_target, proof_targets.iter().map(|(_, t)| t).sum::<u128>());

    // If the list of solutions is empty or the combined proof target is 0, return an empty map.
    if proof_targets.is_empty() || combined_proof_target == 0 {
        return Default::default();
    }

    // Initialize a vector to store the proving rewards.
    let mut rewards = IndexMap::<_, u64>::with_capacity(proof_targets.len());

    // Calculate the rewards for the individual provers.
    for (address, proof_target) in proof_targets {
        // Compute the numerator.
        let numerator = (puzzle_reward as u128).saturating_mul(proof_target);
        // Compute the denominator.
        // Note: We guarantee this denominator cannot be 0 (to prevent a div by 0).
        let denominator = combined_proof_target.max(1);
        // Compute the quotient.
        let quotient = numerator.saturating_div(denominator);
        // Ensure the proving reward is within a safe bound.
        if quotient > MAX_COINBASE_REWARD as u128 {
            error!("Prover reward ({quotient}) is too large - skipping solution from {address}");
            continue;
        }
        // Cast the proving reward as a u64.
        // Note: This '.expect' is guaranteed to be safe, as we ensure the quotient is within a safe bound.
        let prover_reward = u64::try_from(quotient).expect("Prover reward is too large");
        // If there is a proving reward, append it to the vector.
        if prover_reward > 0 {
            // Add the proving reward to the prover.
            let entry = rewards.entry(address).or_default();
            *entry = entry.saturating_add(prover_reward);
        }
    }

    // Return the proving rewards.
    rewards
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::{prelude::TestRng, types::Group};

    use indexmap::indexmap;

    type CurrentNetwork = console::network::Testnet3;

    const ITERATIONS: usize = 1000;

    #[test]
    fn test_staking_rewards() {
        let rng = &mut TestRng::default();
        // Sample a random committee.
        let committee = ledger_committee::test_helpers::sample_committee(rng);
        // Sample a random block reward.
        let block_reward = rng.gen_range(0..MAX_COINBASE_REWARD);
        // Retrieve an address.
        let address = *committee.members().iter().next().unwrap().0;

        for _ in 0..ITERATIONS {
            // Sample a random stake.
            let stake = rng.gen_range(1_000_000..committee.total_stake());
            // Construct the stakers.
            let stakers = indexmap! {address => (address, stake)};
            let rewards = staking_rewards::<CurrentNetwork>(stakers, &committee, block_reward);
            assert_eq!(rewards.len(), 1);
            let (candidate_address, (candidate_validator, candidate_stake)) = rewards.into_iter().next().unwrap();
            assert_eq!(candidate_address, address);
            assert_eq!(candidate_validator, address);
            let reward = block_reward as u128 * stake as u128 / committee.total_stake() as u128;
            assert_eq!(candidate_stake, stake + reward as u64);
        }
    }

    #[test]
    fn test_staking_rewards_cannot_exceed_coinbase_reward() {
        let rng = &mut TestRng::default();
        // Sample a random committee.
        let committee = ledger_committee::test_helpers::sample_committee(rng);
        // Retrieve an address.
        let address = *committee.members().iter().next().unwrap().0;

        // Ensure a staking reward that is too large, renders no rewards.
        for _ in 0..ITERATIONS {
            // Sample a random overly-large block reward.
            let block_reward = rng.gen_range(MAX_COINBASE_REWARD..u64::MAX);
            // Sample a random stake.
            let stake = rng.gen_range(1_000_000..u64::MAX);
            // Check that an overly large block reward fails.
            let rewards =
                staking_rewards::<CurrentNetwork>(indexmap![address => (address, stake)], &committee, block_reward);
            assert!(rewards.is_empty());
        }
    }

    #[test]
    fn test_staking_rewards_is_empty() {
        let rng = &mut TestRng::default();
        // Sample a random committee.
        let committee = ledger_committee::test_helpers::sample_committee(rng);
        // Retrieve an address.
        let address = *committee.members().iter().next().unwrap().0;

        // Compute the staking rewards (empty).
        let rewards = staking_rewards::<CurrentNetwork>(indexmap![], &committee, rng.gen());
        assert!(rewards.is_empty());

        // Check that a maxed out coinbase reward, returns empty.
        let rewards =
            staking_rewards::<CurrentNetwork>(indexmap![address => (address, 1_000_000)], &committee, u64::MAX);
        assert!(rewards.is_empty());
    }

    #[test]
    fn test_proving_rewards() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a random address.
            let address = Address::new(Group::rand(rng));
            // Sample a random puzzle reward.
            let puzzle_reward = rng.gen_range(0..MAX_COINBASE_REWARD);

            let rewards =
                proving_rewards::<CurrentNetwork>(vec![(address, u64::MAX as u128)], puzzle_reward, u64::MAX as u128);
            assert_eq!(rewards.len(), 1);
            let (candidate_address, candidate_amount) = rewards.into_iter().next().unwrap();
            assert_eq!(candidate_address, address);
            assert!(candidate_amount <= puzzle_reward);
        }
    }

    #[test]
    fn test_proving_rewards_cannot_exceed_coinbase_reward() {
        let rng = &mut TestRng::default();

        // Ensure a proving reward that is too large, renders no rewards.
        for _ in 0..ITERATIONS {
            // Sample a random address.
            let address = Address::new(Group::rand(rng));
            // Sample a random overly-large puzzle reward.
            let puzzle_reward = rng.gen_range(MAX_COINBASE_REWARD..u64::MAX);
            // Sample a random proof target.
            let proof_target = rng.gen_range(0..u64::MAX as u128);
            // Check that a maxed out proof target fails.
            let rewards = proving_rewards::<CurrentNetwork>(vec![(address, proof_target)], puzzle_reward, proof_target);
            assert!(rewards.is_empty());
        }
    }

    #[test]
    fn test_proving_rewards_is_empty() {
        let rng = &mut TestRng::default();
        // Sample a random address.
        let address = Address::new(Group::rand(rng));

        // Compute the proving rewards (empty).
        let rewards = proving_rewards::<CurrentNetwork>(vec![], rng.gen(), 0);
        assert!(rewards.is_empty());

        // Check that a maxed out coinbase reward, returns empty.
        let rewards = proving_rewards::<CurrentNetwork>(vec![(address, 2)], u64::MAX, 2);
        assert!(rewards.is_empty());

        // Ensure a 0 coinbase reward case is empty.
        let rewards = proving_rewards::<CurrentNetwork>(vec![(address, 2)], 0, 2);
        assert!(rewards.is_empty());
    }
}
