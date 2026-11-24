module
public import RKCert.Dirk15Replay.N6K1J1W1
public import RKCert.Dirk15Replay.N6K1J2W1

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem R6K1E0 : Order15GoodPrimePair (nodeMomentNorm 6 1 1 1) (nodeMomentNorm 6 1 2 1) 18 18 :=
  goodPrimePair_of_samples FixedReplay.N6K1J1W1.candidate FixedReplay.N6K1J2W1.candidate [174, 978, 644, 446, 320, 637, 1000, 432, 81, 156, 57, 970, 226, 923, 508, 333, 55, 558] [425, 466, 842, 537, 341, 901, 640, 611, 970, 708, 598, 263, 957, 153, 809, 946, 362, 488]
    FixedReplay.N6K1J1W1.exactReduction FixedReplay.N6K1J2W1.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
