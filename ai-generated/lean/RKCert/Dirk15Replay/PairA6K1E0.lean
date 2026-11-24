module
public import RKCert.Dirk15Replay.A6K1J1W0
public import RKCert.Dirk15Replay.A6K1J2W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem A6K1E0 : Order15GoodPrimePair (anchorMomentNorm 6 1 1) (anchorMomentNorm 6 1 2) 1 1 :=
  goodPrimePair_of_samples FixedReplay.A6K1J1W0.candidate FixedReplay.A6K1J2W0.candidate [688] [37]
    FixedReplay.A6K1J1W0.exactReduction FixedReplay.A6K1J2W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
