module
public import RKCert.Dirk15Replay.N5K3J1W0
public import RKCert.Dirk15Replay.N5K3J2W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem F5K3E0 : Order15GoodPrimePair (nodeMomentNorm 5 3 1 0) (nodeMomentNorm 5 3 2 0) 60 60 :=
  goodPrimePair_of_samples FixedReplay.N5K3J1W0.candidate FixedReplay.N5K3J2W0.candidate [401, 115, 582, 551, 639, 656, 603, 659, 929, 41, 74, 841, 380, 753, 424, 246, 195, 413, 959, 989, 394, 710, 197, 216, 701, 948, 115, 856, 307, 244, 601, 712, 788, 60, 1001, 369, 469, 785, 764, 348, 224, 620, 244, 346, 481, 172, 272, 910, 505, 101, 595, 334, 452, 790, 919, 581, 262, 746, 833, 972] [334, 893, 366, 197, 65, 85, 929, 920, 260, 511, 11, 758, 218, 514, 335, 790, 958, 428, 984, 101, 902, 373, 799, 884, 248, 922, 745, 680, 822, 301, 205, 359, 146, 466, 489, 342, 527, 279, 388, 754, 11, 925, 657, 574, 22, 83, 8, 873, 42, 974, 596, 547, 917, 467, 703, 485, 284, 617, 857, 675]
    FixedReplay.N5K3J1W0.exactReduction FixedReplay.N5K3J2W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
