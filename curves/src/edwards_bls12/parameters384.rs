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
    edwards_bls12::{Fq384, Fr253},
    errors::GroupError,
    templates::twisted_edwards_extended::{Affine, Projective},
    traits::{AffineCurve, ModelParameters, MontgomeryParameters, TwistedEdwardsParameters},
};
use snarkvm_fields::field;
use snarkvm_utilities::biginteger::{BigInteger256, BigInteger384};

use std::str::FromStr;

pub type EdwardsAffine384 = Affine<EdwardsParameters384>;
pub type EdwardsProjective384 = Projective<EdwardsParameters384>;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct EdwardsParameters384;

impl ModelParameters for EdwardsParameters384 {
    type BaseField = Fq384;
    type ScalarField = Fr253;
}

impl TwistedEdwardsParameters for EdwardsParameters384 {
    type MontgomeryParameters = EdwardsParameters384;

    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) = (GENERATOR_X, GENERATOR_Y);
    /// B1 = x^2 - 1
    // const B1: Fr253 = field!(
    //     Fr253,
    //     BigInteger256([12574070832645531618, 10005695704657941814, 1564543351912391449, 657300228442948690])
    // );
    /// B2 = x^2
    // const B2: Fr253 = field!(
    //     Fr253,
    //     BigInteger256([2417046298041509844, 11783911742408086824, 14689097366802547462, 270119112518072728])
    // );
    /// COFACTOR = (x - 1)^2 / 3  = 30631250834960419227450344600217059328
    const COFACTOR: &'static [u64] = &[0x0, 0x170b5d4430000000];
    /// COFACTOR_INV = COFACTOR^{-1} mod r
    ///              = 5285428838741532253824584287042945485047145357130994810877
    const COFACTOR_INV: Fr253 = field!(
        Fr253,
        BigInteger256([2013239619100046060, 4201184776506987597, 2526766393982337036, 1114629510922847535,])
    );
    // const PHI: Fq = field!(
    //     Fq,
    //     BigInteger384([
    //         0xdacd106da5847973,
    //         0xd8fe2454bac2a79a,
    //         0x1ada4fd6fd832edc,
    //         0xfb9868449d150908,
    //         0xd63eb8aeea32285e,
    //         0x167d6a36f873fd0,
    //     ])
    // );
    /// R128 = 2^128 - 1
    // const R128: Fr253 = field!(
    //     Fr253,
    //     BigInteger256([13717662654766427599, 14709524173037165000, 15342848074630952979, 736762107895475646])
    // );
    /// EDWARDS_A = -1
    const EDWARDS_A: Fq384 = field!(Fq384, BigInteger384([
        9384023879812382873, 14252412606051516495, 9184438906438551565, 11444845376683159689, 8738795276227363922, 81297770384137296
    ]));
        // field!(Fq384, BigInteger384([0x8cf500000000000e, 0xe75281ef6000000e, 0x49dc37a90b0ba012, 0x55f8b2c6e710ab9, 0, 0]));
    /// EDWARDS_D = 3021
    /// 10884637349400607336
    // 122268283598675559488486339158635529096981886914877139579534153582033676785385790730042363341236035746924960903179
    // cb5d5818b4d2796505bb385732fe3a1bbc34cc60d19690bf8b2d97f059909cb9aeca3c3871e9f27016092b426b700b
    // 7925bf4222538363, f57011bac07d547d
    // 18446744073709551615
    const EDWARDS_D: Fq384 = field!(Fq384, BigInteger384([8729593743492219747, 17685655230474966141, 551337432364730322, 3083704325251882387, 5042730785351324831, 52955784937451845]));
    // const EDWARDS_D: Fq384 = field!(Fq384, BigInteger384([10884637349400607336, 10056813479332698586, 3406039385304768047, 15521605534375526083, 18272470618914989681, 107912150998971165]));
        // field!(Fq384, BigInteger384([0xd047ffffffff5e30, 0xf0a91026ffff57d2, 0x9013f560d102582, 0x9fd242ca7be5700, 0, 0]));

    /// Multiplication by `a` is just negation.
    /// Is `a` 1 or -1?
    #[inline(always)]
    fn mul_by_a(elem: &Self::BaseField) -> Self::BaseField {
        -*elem
    }
}


impl MontgomeryParameters for EdwardsParameters384 {
    type TwistedEdwardsParameters = EdwardsParameters384;

    /// MONTGOMERY_A = 3990301581132929505568273333084066329187552697088022219156688740916631500114
    ///              = 0x8D26E3FADA9010A26949031ECE3971B93952AD84D4753DDEDB748DA37E8F552
    const MONTGOMERY_A: Fq384 = field!(
        Fq384,
        BigInteger384([
            4998116180946001437, 5409451413373758038, 5581492925754928115, 5083985449494384897, 260765002561937696, 26137424653138818
        ])
        // BigInteger384([
        //     13800168384327121454u64,
        //     6841573379969807446u64,
        //     12529593083398462246u64,
        //     853978956621483129u64,
        //     0,
        //     0,
        // ])
    );
    /// MONTGOMERY_B = 4454160168295440918680551605697480202188346638066041608778544715000777738925
    ///              = 0x9D8F71EEC83A44C3A1FBCEC6F5418E5C6154C2682B8AC231C5A3725C8170AAD
    const MONTGOMERY_B: Fq384 = field!(
        Fq384,
        BigInteger384([
            7920084186108633250, 12155202346409073806, 6518651246920890713, 6337560106649019193, 14197095299629383216, 112385837822115092
        ])
        // BigInteger384([
        //     7239382437352637935u64,
        //     14509846070439283655u64,
        //     5083066350480839936u64,
        //     1265663645916442191u64,
        //     0,
        //     0,
        // ])
    );
}


  

///
/// G1_GENERATOR_X =
/// 89363714989903307245735717098563574705733591463163614225748337416674727625843187853442697973404985688481508350822
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bls12_377` for tests.
///
pub const GENERATOR_X: Fq384 = field!(
    Fq384,
    BigInteger384::new([
        1171681672315280277,
        6528257384425852712,
        7514971432460253787,
        2032708395764262463,
        12876543207309632302,
        107509843840671767
    ])
);

///
/// G1_GENERATOR_Y =
/// 3702177272937190650578065972808860481433820514072818216637796320125658674906330993856598323293086021583822603349
///
/// See `snarkvm_algorithms::hash_to_curve::tests::bls12_377` for tests.
///
pub const GENERATOR_Y: Fq384 = field!(
    Fq384,
    BigInteger384::new([
        13572190014569192121,
        15344828677741220784,
        17067903700058808083,
        10342263224753415805,
        1083990386877464092,
        21335464879237822
    ])
);



impl FromStr for EdwardsAffine384 {
    type Err = GroupError;

    fn from_str(mut s: &str) -> Result<Self, Self::Err> {
        s = s.trim();
        if s.is_empty() {
            return Err(GroupError::ParsingEmptyString);
        }
        if s.len() < 3 {
            return Err(GroupError::InvalidString);
        }
        if !(s.starts_with('(') && s.ends_with(')')) {
            return Err(GroupError::InvalidString);
        }
        let mut point = Vec::new();
        for substr in s.split(|c| c == '(' || c == ')' || c == ',' || c == ' ') {
            if !substr.is_empty() {
                point.push(Fq384::from_str(substr)?);
            }
        }
        if point.len() != 2 {
            return Err(GroupError::InvalidGroupElement);
        }
        let point = EdwardsAffine384::new(point[0], point[1], point[0] * point[1]);

        if !point.is_on_curve() { Err(GroupError::InvalidGroupElement) } else { Ok(point) }
    }
}

