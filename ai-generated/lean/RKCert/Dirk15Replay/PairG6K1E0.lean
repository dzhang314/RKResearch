module
public import RKCert.Dirk15Replay.T6K1J1W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem G6K1E0 : Order15GoodPrimePair (parameterGramNorm 6 1 1 0) (minusParameter (parameterGramNorm 6 1 1 0)) 24 24 :=
  goodPrimePair_of_samples FixedReplay.T6K1J1W0.candidate (alternateResidue true FixedReplay.T6K1J1W0.candidate) [78, 628, 327, 755, 498, 10, 30, 165, 950, 289, 348, 372, 962, 671, 755, 38, 625, 639, 935, 751, 458, 428, 780, 488] [78, 381, 327, 254, 498, 999, 30, 844, 950, 720, 348, 637, 962, 338, 755, 971, 625, 370, 935, 258, 458, 581, 780, 521]
    FixedReplay.T6K1J1W0.exactReduction (minusParameter_reduction FixedReplay.T6K1J1W0.exactReduction)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
