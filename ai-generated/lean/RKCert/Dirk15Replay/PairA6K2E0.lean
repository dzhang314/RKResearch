module
public import RKCert.Dirk15Replay.A6K2J1W0
public import RKCert.Dirk15Replay.A6K2J2W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem A6K2E0 : Order15GoodPrimePair (anchorMomentNorm 6 2 1) (anchorMomentNorm 6 2 2) 6 6 :=
  goodPrimePair_of_samples FixedReplay.A6K2J1W0.candidate FixedReplay.A6K2J2W0.candidate [589, 86, 335, 898, 514, 20] [367, 47, 665, 655, 837, 425]
    FixedReplay.A6K2J1W0.exactReduction FixedReplay.A6K2J2W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
