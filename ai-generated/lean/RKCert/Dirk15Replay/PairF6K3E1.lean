module
public import RKCert.Dirk15Replay.N6K3J2W0
public import RKCert.Dirk15Replay.N6K3J3W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem F6K3E1 : Order15GoodPrimePair (nodeMomentNorm 6 3 2 0) (nodeMomentNorm 6 3 3 0) 120 120 :=
  goodPrimePair_of_samples FixedReplay.N6K3J2W0.candidate FixedReplay.N6K3J3W0.candidate [542, 233, 795, 988, 187, 81, 570, 232, 670, 907, 971, 485, 889, 365, 379, 604, 224, 587, 272, 971, 461, 26, 652, 801, 393, 371, 261, 659, 888, 923, 965, 320, 519, 804, 226, 424, 821, 568, 155, 74, 491, 210, 789, 533, 614, 838, 898, 952, 107, 232, 100, 969, 551, 606, 217, 892, 999, 975, 889, 445, 824, 794, 938, 963, 785, 55, 821, 994, 541, 510, 395, 24, 661, 314, 86, 685, 591, 806, 331, 290, 102, 967, 479, 699, 68, 972, 135, 104, 88, 40, 46, 155, 502, 712, 644, 810, 903, 540, 634, 929, 649, 355, 420, 868, 478, 270, 306, 392, 466, 63, 255, 316, 766, 80, 145, 650, 255, 442, 27, 787] [526, 375, 430, 533, 485, 126, 533, 905, 790, 593, 450, 105, 194, 159, 390, 485, 79, 542, 997, 457, 549, 242, 518, 754, 780, 578, 737, 3, 641, 732, 937, 217, 30, 323, 233, 743, 423, 736, 487, 542, 542, 60, 938, 832, 90, 433, 516, 809, 951, 383, 789, 7, 887, 903, 808, 504, 210, 732, 299, 995, 881, 905, 138, 804, 104, 931, 897, 749, 868, 185, 588, 883, 587, 379, 441, 958, 608, 325, 167, 292, 703, 47, 971, 330, 862, 520, 336, 167, 223, 249, 570, 391, 941, 36, 364, 46, 291, 777, 644, 466, 589, 433, 256, 707, 50, 214, 814, 555, 855, 53, 756, 417, 750, 632, 93, 480, 217, 893, 832, 328]
    FixedReplay.N6K3J2W0.exactReduction FixedReplay.N6K3J3W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
