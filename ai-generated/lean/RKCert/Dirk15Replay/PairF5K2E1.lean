module
public import RKCert.Dirk15Replay.N5K2J2W0
public import RKCert.Dirk15Replay.N5K2J3W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem F5K2E1 : Order15GoodPrimePair (nodeMomentNorm 5 2 2 0) (nodeMomentNorm 5 2 3 0) 40 40 :=
  goodPrimePair_of_samples FixedReplay.N5K2J2W0.candidate FixedReplay.N5K2J3W0.candidate [914, 992, 606, 178, 658, 926, 917, 192, 894, 553, 197, 261, 540, 459, 44, 444, 829, 290, 617, 507, 420, 330, 675, 630, 522, 793, 65, 833, 342, 350, 911, 479, 727, 883, 172, 366, 654, 257, 762, 811] [278, 65, 461, 989, 317, 611, 264, 2, 796, 600, 236, 305, 816, 263, 591, 639, 422, 1006, 715, 922, 339, 461, 666, 294, 462, 101, 820, 8, 258, 746, 132, 164, 600, 20, 151, 73, 26, 284, 682, 367]
    FixedReplay.N5K2J2W0.exactReduction FixedReplay.N5K2J3W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
