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

#![cfg_attr(nightly, doc = include_str!("../../documentation/the_aleo_curves/01_edwards_bls12.md"))]

pub mod fq;
#[doc(inline)]
pub use fq::*;

pub mod fq384;
#[doc(inline)]
pub use fq384::*;

pub mod fr;
#[doc(inline)]
pub use fr::*;

pub mod fr253;
#[doc(inline)]
pub use fr253::*;

pub mod parameters;
#[doc(inline)]
pub use parameters::*;

pub mod parameters384;
#[doc(inline)]
pub use parameters384::*;

#[cfg(test)]
mod tests;
