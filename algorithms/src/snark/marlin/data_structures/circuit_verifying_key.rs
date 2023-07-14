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

use crate::{fft::EvaluationDomain, polycommit::sonic_pc, r1cs::SynthesisError, snark::marlin::ahp::indexer::*};
use snarkvm_curves::PairingEngine;
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};
use snarkvm_utilities::{
    error,
    io::{self, Read, Write},
    serialize::*,
    string::String,
    FromBytes,
    FromBytesDeserializer,
    ToBytes,
    ToBytesSerializer,
    ToMinimalBits,
};

use anyhow::Result;
use core::{fmt, str::FromStr};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::cmp::Ordering;

/// Verification key for a specific index (i.e., R1CS matrices).
#[derive(Debug, Clone, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct CircuitVerifyingKey<E: PairingEngine> {
    /// Stores information about the size of the circuit, as well as its defined field.
    pub circuit_info: CircuitInfo,
    /// Commitments to the indexed polynomials.
    pub circuit_commitments: Vec<sonic_pc::Commitment<E>>,
    pub id: CircuitId,
}

impl<E: PairingEngine> ToMinimalBits for CircuitVerifyingKey<E> {
    fn to_minimal_bits(&self) -> Vec<bool> {
        let constraint_domain = EvaluationDomain::<E::Fr>::new(self.circuit_info.num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)
            .unwrap();
        let non_zero_domain_a = EvaluationDomain::<E::Fr>::new(self.circuit_info.num_non_zero_a)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)
            .unwrap();
        let non_zero_domain_b = EvaluationDomain::<E::Fr>::new(self.circuit_info.num_non_zero_b)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)
            .unwrap();
        let non_zero_domain_c = EvaluationDomain::<E::Fr>::new(self.circuit_info.num_non_zero_c)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)
            .unwrap();

        assert!(constraint_domain.size() < u64::MAX as usize);
        assert!(non_zero_domain_a.size() < u64::MAX as usize);
        assert!(non_zero_domain_b.size() < u64::MAX as usize);
        assert!(non_zero_domain_c.size() < u64::MAX as usize);

        let constraint_domain_size = constraint_domain.size() as u64;
        let non_zero_domain_a_size = non_zero_domain_a.size() as u64;
        let non_zero_domain_b_size = non_zero_domain_b.size() as u64;
        let non_zero_domain_c_size = non_zero_domain_c.size() as u64;

        let constraint_domain_size_bits = constraint_domain_size
            .to_le_bytes()
            .iter()
            .flat_map(|&byte| (0..8).map(move |i| (byte >> i) & 1u8 == 1u8))
            .collect::<Vec<bool>>();
        let non_zero_domain_size_a_bits = non_zero_domain_a_size
            .to_le_bytes()
            .iter()
            .flat_map(|&byte| (0..8).map(move |i| (byte >> i) & 1u8 == 1u8))
            .collect::<Vec<bool>>();
        let non_zero_domain_size_b_bits = non_zero_domain_b_size
            .to_le_bytes()
            .iter()
            .flat_map(|&byte| (0..8).map(move |i| (byte >> i) & 1u8 == 1u8))
            .collect::<Vec<bool>>();
        let non_zero_domain_size_c_bits = non_zero_domain_c_size
            .to_le_bytes()
            .iter()
            .flat_map(|&byte| (0..8).map(move |i| (byte >> i) & 1u8 == 1u8))
            .collect::<Vec<bool>>();

        let circuit_commitments_bits = self.circuit_commitments.to_minimal_bits();

        [
            constraint_domain_size_bits,
            non_zero_domain_size_a_bits,
            non_zero_domain_size_b_bits,
            non_zero_domain_size_c_bits,
            circuit_commitments_bits,
        ]
        .concat()
    }
}

impl<E: PairingEngine> FromBytes for CircuitVerifyingKey<E> {
    fn read_le<R: Read>(r: R) -> io::Result<Self> {
        Self::deserialize_compressed(r).map_err(|_| error("could not deserialize CircuitVerifyingKey"))
    }
}

impl<E: PairingEngine> ToBytes for CircuitVerifyingKey<E> {
    fn write_le<W: Write>(&self, w: W) -> io::Result<()> {
        self.serialize_compressed(w).map_err(|_| error("could not serialize CircuitVerifyingKey"))
    }
}

impl<E: PairingEngine> CircuitVerifyingKey<E> {
    /// Iterate over the commitments to indexed polynomials in `self`.
    pub fn iter(&self) -> impl Iterator<Item = &sonic_pc::Commitment<E>> {
        self.circuit_commitments.iter()
    }
}

impl<E: PairingEngine> ToConstraintField<E::Fq> for CircuitVerifyingKey<E> {
    fn to_field_elements(&self) -> Result<Vec<E::Fq>, ConstraintFieldError> {
        let constraint_domain_size =
            EvaluationDomain::<E::Fr>::compute_size_of_domain(self.circuit_info.num_constraints).unwrap() as u128;
        let non_zero_a_domain_size =
            EvaluationDomain::<E::Fr>::compute_size_of_domain(self.circuit_info.num_non_zero_a).unwrap() as u128;
        let non_zero_b_domain_size =
            EvaluationDomain::<E::Fr>::compute_size_of_domain(self.circuit_info.num_non_zero_b).unwrap() as u128;
        let non_zero_c_domain_size =
            EvaluationDomain::<E::Fr>::compute_size_of_domain(self.circuit_info.num_non_zero_c).unwrap() as u128;

        let mut res = Vec::new();
        res.append(&mut E::Fq::from(constraint_domain_size).to_field_elements()?);
        res.append(&mut E::Fq::from(non_zero_a_domain_size).to_field_elements()?);
        res.append(&mut E::Fq::from(non_zero_b_domain_size).to_field_elements()?);
        res.append(&mut E::Fq::from(non_zero_c_domain_size).to_field_elements()?);
        for comm in self.circuit_commitments.iter() {
            res.append(&mut comm.to_field_elements()?);
        }

        // Intentionally ignore the appending of the PC verifier key.

        Ok(res)
    }
}

impl<E: PairingEngine> FromStr for CircuitVerifyingKey<E> {
    type Err = anyhow::Error;

    #[inline]
    fn from_str(vk_hex: &str) -> Result<Self, Self::Err> {
        Self::from_bytes_le(&hex::decode(vk_hex)?)
    }
}

impl<E: PairingEngine> fmt::Display for CircuitVerifyingKey<E> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let vk_hex = hex::encode(self.to_bytes_le().expect("Failed to convert verifying key to bytes"));
        write!(f, "{vk_hex}")
    }
}

impl<E: PairingEngine> Serialize for CircuitVerifyingKey<E> {
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, E: PairingEngine> Deserialize<'de> for CircuitVerifyingKey<E> {
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let s: String = Deserialize::deserialize(deserializer)?;
                FromStr::from_str(&s).map_err(de::Error::custom)
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "verifying key"),
        }
    }
}

impl<E: PairingEngine> Ord for CircuitVerifyingKey<E> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.id.cmp(&other.id)
    }
}

impl<E: PairingEngine> PartialOrd for CircuitVerifyingKey<E> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
