module
public import RKCert.Dirk15Replay.N6K1J1W0
public import RKCert.Dirk15Replay.N6K1J2W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem F6K1E0 : Order15GoodPrimePair (nodeMomentNorm 6 1 1 0) (nodeMomentNorm 6 1 2 0) 12 12 :=
  goodPrimePair_of_samples FixedReplay.N6K1J1W0.candidate FixedReplay.N6K1J2W0.candidate [206, 859, 550, 117, 892, 659, 481, 94, 215, 835, 946, 959] [565, 92, 268, 596, 477, 321, 997, 338, 594, 633, 136, 710]
    FixedReplay.N6K1J1W0.exactReduction FixedReplay.N6K1J2W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
