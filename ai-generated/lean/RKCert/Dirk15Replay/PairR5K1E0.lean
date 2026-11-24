module
public import RKCert.Dirk15Replay.N5K1J1W1
public import RKCert.Dirk15Replay.N5K1J2W1

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem R5K1E0 : Order15GoodPrimePair (nodeMomentNorm 5 1 1 1) (nodeMomentNorm 5 1 2 1) 15 15 :=
  goodPrimePair_of_samples FixedReplay.N5K1J1W1.candidate FixedReplay.N5K1J2W1.candidate [877, 802, 389, 707, 985, 106, 547, 661, 288, 820, 901, 219, 193, 918, 979] [634, 484, 315, 677, 807, 686, 167, 614, 0, 406, 256, 378, 863, 842, 196]
    FixedReplay.N5K1J1W1.exactReduction FixedReplay.N5K1J2W1.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
