module
public import RKCert.Dirk15Replay.A5K1J1W0
public import RKCert.Dirk15Replay.A5K1J2W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem A5K1E0 : Order15GoodPrimePair (anchorMomentNorm 5 1 1) (anchorMomentNorm 5 1 2) 1 1 :=
  goodPrimePair_of_samples FixedReplay.A5K1J1W0.candidate FixedReplay.A5K1J2W0.candidate [778] [765]
    FixedReplay.A5K1J1W0.exactReduction FixedReplay.A5K1J2W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
