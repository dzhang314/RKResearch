module
public import RKCert.Dirk15FirstReplayPair
public import RKCert.Dirk15Replay.N5K1J3W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem F5K1E1 : Order15GoodPrimePair (nodeMomentNorm 5 1 2 0) (nodeMomentNorm 5 1 3 0) 10 10 :=
  goodPrimePair_of_samples Order15Smoke.J2.candidate FixedReplay.N5K1J3W0.candidate [112, 362, 1002, 50, 47, 710, 130, 209, 670, 639] [629, 749, 625, 871, 928, 591, 341, 370, 108, 63]
    Order15Smoke.J2.exactReduction FixedReplay.N5K1J3W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
