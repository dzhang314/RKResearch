module
public import RKCert.Dirk15Replay.N6K3J1W1
public import RKCert.Dirk15Replay.N6K3J2W1

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem R6K3E0 : Order15GoodPrimePair (nodeMomentNorm 6 3 1 1) (nodeMomentNorm 6 3 2 1) 140 140 :=
  goodPrimePair_of_samples FixedReplay.N6K3J1W1.candidate FixedReplay.N6K3J2W1.candidate [347, 55, 211, 58, 661, 546, 480, 134, 866, 698, 555, 514, 121, 99, 369, 453, 157, 466, 156, 13, 854, 263, 975, 127, 479, 702, 800, 604, 877, 940, 502, 571, 794, 818, 437, 129, 620, 806, 832, 449, 717, 541, 50, 313, 153, 466, 825, 931, 149, 279, 952, 168, 850, 826, 784, 848, 864, 67, 436, 766, 327, 879, 978, 296, 784, 792, 590, 320, 503, 943, 391, 850, 680, 276, 588, 779, 263, 320, 645, 82, 643, 611, 766, 361, 768, 232, 100, 235, 876, 615, 953, 204, 233, 127, 812, 724, 883, 577, 305, 780, 58, 618, 170, 821, 885, 684, 908, 79, 417, 738, 292, 411, 350, 38, 437, 365, 180, 473, 100, 215, 507, 485, 974, 547, 330, 796, 614, 733, 884, 407, 362, 370, 175, 426, 529, 891, 66, 526, 396, 672] [382, 60, 248, 256, 964, 795, 648, 105, 280, 620, 537, 699, 398, 518, 684, 849, 598, 161, 711, 886, 817, 907, 335, 583, 480, 804, 42, 608, 723, 264, 135, 673, 203, 914, 142, 532, 582, 527, 324, 12, 423, 677, 110, 515, 921, 599, 184, 788, 965, 542, 31, 795, 592, 102, 346, 111, 482, 907, 892, 893, 65, 169, 285, 834, 378, 97, 290, 479, 733, 773, 15, 878, 965, 781, 103, 943, 228, 576, 698, 955, 964, 409, 0, 174, 5, 314, 991, 883, 783, 821, 319, 234, 330, 528, 813, 933, 524, 476, 169, 978, 1000, 336, 705, 760, 350, 47, 737, 810, 911, 655, 592, 408, 67, 10, 564, 5, 591, 135, 445, 331, 969, 164, 641, 629, 614, 382, 359, 154, 232, 14, 866, 478, 962, 770, 479, 365, 36, 417, 697, 507]
    FixedReplay.N6K3J1W1.exactReduction FixedReplay.N6K3J2W1.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
