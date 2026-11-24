module
public import RKCert.Dirk15Replay.A5K2J1W0
public import RKCert.Dirk15Replay.A5K2J2W0

@[expose] public section

namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem A5K2E0 : Order15GoodPrimePair (anchorMomentNorm 5 2 1) (anchorMomentNorm 5 2 2) 5 5 :=
  goodPrimePair_of_samples FixedReplay.A5K2J1W0.candidate FixedReplay.A5K2J2W0.candidate [789, 532, 707, 156, 843] [712, 357, 126, 370, 320]
    FixedReplay.A5K2J1W0.exactReduction FixedReplay.A5K2J2W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
