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

use crate::{
    helpers::rocksdb::{
        internal::{self, DataMap, Database},
        BlockMap,
        MapID,
        TransactionDB,
        TransitionDB,
    },
    BlockStorage,
    ConfirmedTxType,
    TransactionStore,
    TransitionStore,
};
use console::{account::Signature, prelude::*};
use ledger_block::{Header, Ratify};
use ledger_coinbase::{CoinbaseSolution, PuzzleCommitment};

/// A RocksDB block storage.
#[derive(Clone)]
pub struct BlockDB<N: Network> {
    /// The mapping of `block height` to `state root`.
    state_root_map: DataMap<u32, N::StateRoot>,
    /// The mapping of `state root` to `block height`.
    reverse_state_root_map: DataMap<N::StateRoot, u32>,
    /// The mapping of `block height` to `block hash`.
    id_map: DataMap<u32, N::BlockHash>,
    /// The mapping of `block hash` to `block height`.
    reverse_id_map: DataMap<N::BlockHash, u32>,
    /// The header map.
    header_map: DataMap<N::BlockHash, Header<N>>,
    /// The transactions map.
    transactions_map: DataMap<N::BlockHash, Vec<N::TransactionID>>,
    /// The confirmed transactions map.
    confirmed_transactions_map: DataMap<N::TransactionID, (N::BlockHash, ConfirmedTxType, Vec<u8>)>,
    /// The transaction store.
    transaction_store: TransactionStore<N, TransactionDB<N>>,
    /// The ratifications map.
    ratifications_map: DataMap<N::BlockHash, Vec<Ratify<N>>>,
    /// The coinbase solution map.
    coinbase_solution_map: DataMap<N::BlockHash, Option<CoinbaseSolution<N>>>,
    /// The coinbase puzzle commitment map.
    coinbase_puzzle_commitment_map: DataMap<PuzzleCommitment<N>, u32>,
    /// The signature map.
    signature_map: DataMap<N::BlockHash, Signature<N>>,
}

#[rustfmt::skip]
impl<N: Network> BlockStorage<N> for BlockDB<N> {
    type StateRootMap = DataMap<u32, N::StateRoot>;
    type ReverseStateRootMap = DataMap<N::StateRoot, u32>;
    type IDMap = DataMap<u32, N::BlockHash>;
    type ReverseIDMap = DataMap<N::BlockHash, u32>;
    type HeaderMap = DataMap<N::BlockHash, Header<N>>;
    type TransactionsMap = DataMap<N::BlockHash, Vec<N::TransactionID>>;
    type ConfirmedTransactionsMap = DataMap<N::TransactionID, (N::BlockHash, ConfirmedTxType, Vec<u8>)>;
    type TransactionStorage = TransactionDB<N>;
    type TransitionStorage = TransitionDB<N>;
    type RatificationsMap = DataMap<N::BlockHash, Vec<Ratify<N>>>;
    type CoinbaseSolutionMap = DataMap<N::BlockHash, Option<CoinbaseSolution<N>>>;
    type CoinbasePuzzleCommitmentMap = DataMap<PuzzleCommitment<N>, u32>;
    type SignatureMap = DataMap<N::BlockHash, Signature<N>>;

    /// Initializes the block storage.
    fn open(dev: Option<u16>) -> Result<Self> {
        // Initialize the transition store.
        let transition_store = TransitionStore::<N, TransitionDB<N>>::open(dev)?;
        // Initialize the transaction store.
        let transaction_store = TransactionStore::<N, TransactionDB<N>>::open(transition_store)?;
        // Return the block storage.
        Ok(Self {
            state_root_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::StateRoot))?,
            reverse_state_root_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::ReverseStateRoot))?,
            id_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::ID))?,
            reverse_id_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::ReverseID))?,
            header_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::Header))?,
            transactions_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::Transactions))?,
            confirmed_transactions_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::ConfirmedTransactions))?,
            transaction_store,
            ratifications_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::Ratifications))?,
            coinbase_solution_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::CoinbaseSolution))?,
            coinbase_puzzle_commitment_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::CoinbasePuzzleCommitment))?,
            signature_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::Signature))?,
        })
    }

    /// Returns the state root map.
    fn state_root_map(&self) -> &Self::StateRootMap {
        &self.state_root_map
    }

    /// Returns the reverse state root map.
    fn reverse_state_root_map(&self) -> &Self::ReverseStateRootMap {
        &self.reverse_state_root_map
    }

    /// Returns the ID map.
    fn id_map(&self) -> &Self::IDMap {
        &self.id_map
    }

    /// Returns the reverse ID map.
    fn reverse_id_map(&self) -> &Self::ReverseIDMap {
        &self.reverse_id_map
    }

    /// Returns the header map.
    fn header_map(&self) -> &Self::HeaderMap {
        &self.header_map
    }

    /// Returns the transactions map.
    fn transactions_map(&self) -> &Self::TransactionsMap {
        &self.transactions_map
    }

    /// Returns the confirmed transactions map.
    fn confirmed_transactions_map(&self) -> &Self::ConfirmedTransactionsMap {
        &self.confirmed_transactions_map
    }

    /// Returns the transaction store.
    fn transaction_store(&self) -> &TransactionStore<N, Self::TransactionStorage> {
        &self.transaction_store
    }

    /// Returns the ratifications map.
    fn ratifications_map(&self) -> &Self::RatificationsMap {
        &self.ratifications_map
    }

    /// Returns the coinbase solution map.
    fn coinbase_solution_map(&self) -> &Self::CoinbaseSolutionMap {
        &self.coinbase_solution_map
    }

    /// Returns the coinbase puzzle commitment map.
    fn coinbase_puzzle_commitment_map(&self) -> &Self::CoinbasePuzzleCommitmentMap {
        &self.coinbase_puzzle_commitment_map
    }

    /// Returns the signature map.
    fn signature_map(&self) -> &Self::SignatureMap {
        &self.signature_map
    }
}
