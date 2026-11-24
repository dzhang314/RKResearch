module
public import RKCert.Dirk15Replay.N6K2J1W0
public import RKCert.Dirk15Replay.N6K2J2W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem F6K2E0 : Order15GoodPrimePair (nodeMomentNorm 6 2 1 0) (nodeMomentNorm 6 2 2 0) 60 60 :=
  goodPrimePair_of_samples FixedReplay.N6K2J1W0.candidate FixedReplay.N6K2J2W0.candidate [15, 289, 964, 257, 838, 372, 469, 850, 872, 832, 10, 247, 476, 883, 340, 193, 522, 839, 992, 80, 665, 997, 569, 892, 19, 180, 283, 426, 887, 1000, 306, 449, 328, 231, 820, 383, 97, 876, 488, 472, 251, 548, 896, 172, 188, 911, 915, 767, 685, 560, 343, 983, 564, 87, 843, 50, 311, 230, 816, 567] [35, 614, 752, 472, 971, 742, 883, 60, 359, 40, 119, 930, 733, 929, 638, 57, 494, 503, 399, 97, 213, 729, 90, 260, 898, 349, 310, 918, 473, 71, 289, 884, 881, 6, 140, 725, 941, 84, 455, 373, 728, 45, 251, 89, 476, 57, 747, 473, 881, 527, 935, 235, 777, 94, 544, 496, 252, 152, 335, 882]
    FixedReplay.N6K2J1W0.exactReduction FixedReplay.N6K2J2W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
