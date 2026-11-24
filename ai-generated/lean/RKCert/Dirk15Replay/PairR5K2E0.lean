module
public import RKCert.Dirk15Replay.N5K2J1W1
public import RKCert.Dirk15Replay.N5K2J2W1

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem R5K2E0 : Order15GoodPrimePair (nodeMomentNorm 5 2 1 1) (nodeMomentNorm 5 2 2 1) 50 50 :=
  goodPrimePair_of_samples FixedReplay.N5K2J1W1.candidate FixedReplay.N5K2J2W1.candidate [52, 250, 124, 473, 955, 596, 962, 302, 130, 141, 863, 258, 946, 5, 729, 570, 650, 498, 8, 466, 652, 200, 486, 973, 235, 411, 699, 654, 537, 296, 751, 732, 457, 897, 10, 539, 200, 927, 576, 156, 81, 626, 253, 953, 507, 56, 191, 4, 553, 361] [662, 691, 787, 693, 505, 210, 743, 300, 381, 566, 550, 379, 297, 588, 965, 489, 863, 558, 163, 22, 722, 93, 724, 768, 865, 640, 252, 343, 754, 308, 215, 643, 110, 195, 59, 308, 797, 949, 623, 47, 345, 43, 438, 558, 213, 165, 890, 956, 806, 559]
    FixedReplay.N5K2J1W1.exactReduction FixedReplay.N5K2J2W1.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
