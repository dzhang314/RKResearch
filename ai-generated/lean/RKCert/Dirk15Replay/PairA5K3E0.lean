module
public import RKCert.Dirk15Replay.A5K3J1W0
public import RKCert.Dirk15Replay.A5K3J2W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem A5K3E0 : Order15GoodPrimePair (anchorMomentNorm 5 3 1) (anchorMomentNorm 5 3 2) 10 10 :=
  goodPrimePair_of_samples FixedReplay.A5K3J1W0.candidate FixedReplay.A5K3J2W0.candidate [464, 459, 597, 759, 956, 888, 95, 582, 131, 142] [334, 555, 823, 727, 645, 595, 477, 325, 116, 421]
    FixedReplay.A5K3J1W0.exactReduction FixedReplay.A5K3J2W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
