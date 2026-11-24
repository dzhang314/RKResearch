module
public import RKCert.Dirk15Replay.N5K2J1W0
public import RKCert.Dirk15Replay.N5K2J2W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem F5K2E0 : Order15GoodPrimePair (nodeMomentNorm 5 2 1 0) (nodeMomentNorm 5 2 2 0) 40 40 :=
  goodPrimePair_of_samples FixedReplay.N5K2J1W0.candidate FixedReplay.N5K2J2W0.candidate [959, 686, 282, 521, 105, 986, 971, 474, 58, 435, 14, 281, 540, 599, 199, 880, 177, 401, 756, 820, 682, 758, 1002, 936, 4, 914, 563, 239, 742, 353, 717, 628, 761, 831, 494, 611, 153, 903, 560, 774] [815, 362, 336, 578, 275, 431, 809, 311, 530, 116, 738, 807, 339, 161, 700, 956, 657, 462, 37, 845, 438, 825, 150, 500, 950, 645, 762, 373, 722, 109, 36, 255, 252, 895, 623, 675, 762, 402, 220, 905]
    FixedReplay.N5K2J1W0.exactReduction FixedReplay.N5K2J2W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
