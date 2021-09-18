// Copyright (C) 2019-2021 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use crate::{
    record::encrypted::*,
    testnet2::*,
    Account,
    AccountScheme,
    Network,
    NoopProgram,
    Payload,
    ProgramScheme,
    Record,
    ViewKey,
    PAYLOAD_SIZE,
};
use snarkvm_algorithms::traits::{CommitmentScheme, CRH};
use snarkvm_utilities::{FromBytes, UniformRand};

use rand::{Rng, SeedableRng};
use rand_chacha::ChaChaRng;

pub(crate) const ITERATIONS: usize = 25;

#[test]
fn test_record_encryption() {
    let mut rng = ChaChaRng::seed_from_u64(1231275789u64);

    let noop_program = NoopProgram::<Testnet2>::setup(&mut rng).unwrap();

    for _ in 0..ITERATIONS {
        let dummy_account = Account::<Testnet2>::new(&mut rng).unwrap();

        let value = rng.gen();
        let mut payload = [0u8; PAYLOAD_SIZE];
        rng.fill(&mut payload);

        // Sample a new record commitment randomness.
        let commitment_randomness =
            <<Testnet2 as Network>::CommitmentScheme as CommitmentScheme>::Randomness::rand(&mut rng);

        let given_record = Record::new_input(
            noop_program.program_id(),
            dummy_account.address,
            false,
            value,
            Payload::from_bytes_le(&payload).unwrap(),
            <Testnet2 as Network>::serial_number_nonce_crh()
                .hash(&rng.gen::<[u8; 32]>())
                .unwrap(),
            commitment_randomness,
        )
        .unwrap();

        // Encrypt the record
        let (encryped_record, _) = EncryptedRecord::encrypt(&given_record, &mut rng).unwrap();
        let account_view_key = ViewKey::from_private_key(&dummy_account.private_key()).unwrap();

        // Decrypt the record
        let decrypted_record = encryped_record.decrypt(&account_view_key).unwrap();

        assert_eq!(given_record, decrypted_record);
    }
}
