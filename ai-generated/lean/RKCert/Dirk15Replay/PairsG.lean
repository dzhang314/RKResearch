module
public import RKCert.Dirk15Replay.T5K1J1W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem G5K1E0 : Order15GoodPrimePair (parameterGramNorm 5 1 1 0) (minusParameter (parameterGramNorm 5 1 1 0)) 20 20 :=
  goodPrimePair_of_samples FixedReplay.T5K1J1W0.candidate (alternateResidue true FixedReplay.T5K1J1W0.candidate) [147, 1005, 866, 106, 478, 705, 32, 758, 798, 114, 63, 352, 539, 476, 944, 378, 308, 643, 116, 196] [147, 4, 866, 903, 478, 304, 32, 251, 798, 895, 63, 657, 539, 533, 944, 631, 308, 366, 116, 813]
    FixedReplay.T5K1J1W0.exactReduction (minusParameter_reduction FixedReplay.T5K1J1W0.exactReduction)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
