module
public import RKCert.Dirk15Replay.A6K4J1W0
public import RKCert.Dirk15Replay.A6K4J2W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem A6K4E0 : Order15GoodPrimePair (anchorMomentNorm 6 4 1) (anchorMomentNorm 6 4 2) 20 20 :=
  goodPrimePair_of_samples FixedReplay.A6K4J1W0.candidate FixedReplay.A6K4J2W0.candidate [165, 264, 391, 481, 828, 79, 351, 574, 661, 807, 336, 862, 236, 508, 803, 60, 284, 111, 641, 900] [282, 107, 728, 268, 42, 858, 19, 150, 878, 172, 547, 185, 464, 119, 15, 412, 185, 859, 943, 42]
    FixedReplay.A6K4J1W0.exactReduction FixedReplay.A6K4J2W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
