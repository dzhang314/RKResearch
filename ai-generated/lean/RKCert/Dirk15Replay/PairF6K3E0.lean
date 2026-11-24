module
public import RKCert.Dirk15Replay.N6K3J1W0
public import RKCert.Dirk15Replay.N6K3J2W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem F6K3E0 : Order15GoodPrimePair (nodeMomentNorm 6 3 1 0) (nodeMomentNorm 6 3 2 0) 120 120 :=
  goodPrimePair_of_samples FixedReplay.N6K3J1W0.candidate FixedReplay.N6K3J2W0.candidate [305, 394, 271, 709, 343, 388, 642, 161, 624, 318, 888, 957, 28, 719, 189, 160, 519, 712, 943, 753, 772, 257, 3, 350, 820, 672, 965, 601, 1006, 217, 943, 457, 502, 506, 908, 788, 309, 82, 641, 472, 659, 463, 568, 869, 789, 307, 367, 67, 476, 59, 519, 4, 121, 357, 243, 764, 771, 944, 283, 948, 177, 523, 479, 654, 48, 846, 378, 79, 330, 41, 701, 917, 83, 19, 250, 763, 866, 948, 662, 666, 666, 927, 113, 231, 6, 615, 28, 34, 55, 794, 397, 587, 490, 884, 236, 126, 650, 728, 804, 972, 488, 560, 918, 474, 704, 453, 869, 910, 999, 611, 862, 63, 564, 725, 645, 457, 48, 329, 51, 476] [981, 624, 57, 716, 40, 309, 431, 564, 267, 774, 909, 562, 885, 394, 567, 205, 449, 909, 653, 213, 902, 938, 492, 198, 2, 932, 914, 429, 683, 271, 590, 99, 659, 964, 809, 258, 189, 940, 860, 623, 124, 278, 542, 711, 419, 552, 775, 179, 355, 620, 610, 342, 923, 320, 94, 764, 16, 108, 790, 49, 847, 976, 261, 72, 1001, 202, 793, 89, 216, 607, 746, 143, 727, 672, 915, 843, 958, 32, 279, 768, 233, 406, 534, 60, 3, 324, 831, 376, 759, 962, 451, 523, 766, 241, 708, 498, 662, 211, 868, 279, 200, 123, 857, 496, 248, 145, 882, 709, 331, 268, 704, 178, 509, 585, 402, 904, 619, 389, 252, 440]
    FixedReplay.N6K3J1W0.exactReduction FixedReplay.N6K3J2W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
