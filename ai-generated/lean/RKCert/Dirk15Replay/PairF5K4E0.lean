module
public import RKCert.Dirk15Replay.N5K4J1W0
public import RKCert.Dirk15Replay.N5K4J2W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem F5K4E0 : Order15GoodPrimePair (nodeMomentNorm 5 4 1 0) (nodeMomentNorm 5 4 2 0) 40 40 :=
  goodPrimePair_of_samples FixedReplay.N5K4J1W0.candidate FixedReplay.N5K4J2W0.candidate [445, 970, 88, 268, 254, 128, 519, 789, 651, 252, 11, 805, 528, 707, 184, 187, 132, 793, 504, 194, 958, 379, 46, 654, 664, 21, 175, 491, 443, 1001, 843, 434, 115, 168, 762, 298, 282, 131, 325, 888] [39, 735, 101, 277, 208, 917, 793, 839, 849, 986, 757, 372, 701, 242, 883, 146, 393, 511, 143, 854, 370, 811, 192, 16, 576, 477, 934, 742, 686, 494, 478, 489, 957, 816, 739, 470, 670, 945, 82, 980]
    FixedReplay.N5K4J1W0.exactReduction FixedReplay.N5K4J2W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
