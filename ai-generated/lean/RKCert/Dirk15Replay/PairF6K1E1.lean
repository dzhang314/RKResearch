module
public import RKCert.Dirk15Replay.N6K1J2W0
public import RKCert.Dirk15Replay.N6K1J3W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem F6K1E1 : Order15GoodPrimePair (nodeMomentNorm 6 1 2 0) (nodeMomentNorm 6 1 3 0) 12 12 :=
  goodPrimePair_of_samples FixedReplay.N6K1J2W0.candidate FixedReplay.N6K1J3W0.candidate [371, 571, 241, 198, 614, 592, 459, 168, 332, 529, 144, 343] [602, 994, 641, 733, 105, 809, 578, 572, 620, 720, 239, 394]
    FixedReplay.N6K1J2W0.exactReduction FixedReplay.N6K1J3W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
