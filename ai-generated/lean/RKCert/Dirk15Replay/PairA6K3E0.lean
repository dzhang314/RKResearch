module
public import RKCert.Dirk15Replay.A6K3J1W0
public import RKCert.Dirk15Replay.A6K3J2W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem A6K3E0 : Order15GoodPrimePair (anchorMomentNorm 6 3 1) (anchorMomentNorm 6 3 2) 15 15 :=
  goodPrimePair_of_samples FixedReplay.A6K3J1W0.candidate FixedReplay.A6K3J2W0.candidate [245, 40, 979, 47, 193, 998, 191, 454, 564, 88, 537, 882, 41, 627, 85] [367, 242, 163, 747, 252, 71, 756, 505, 944, 55, 126, 112, 298, 544, 730]
    FixedReplay.A6K3J1W0.exactReduction FixedReplay.A6K3J2W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
