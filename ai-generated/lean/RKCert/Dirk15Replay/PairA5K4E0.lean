module
public import RKCert.Dirk15Replay.A5K4J1W0
public import RKCert.Dirk15Replay.A5K4J2W0

@[expose] public section

namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem A5K4E0 : Order15GoodPrimePair (anchorMomentNorm 5 4 1) (anchorMomentNorm 5 4 2) 10 10 :=
  goodPrimePair_of_samples FixedReplay.A5K4J1W0.candidate FixedReplay.A5K4J2W0.candidate [220, 390, 484, 509, 628, 292, 560, 330, 286, 71] [1006, 45, 181, 74, 450, 175, 6, 761, 717, 770]
    FixedReplay.A5K4J1W0.exactReduction FixedReplay.A5K4J2W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
