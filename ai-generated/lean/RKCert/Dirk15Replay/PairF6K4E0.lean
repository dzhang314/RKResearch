module
public import RKCert.Dirk15Replay.N6K4J1W0
public import RKCert.Dirk15Replay.N6K4J2W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem F6K4E0 : Order15GoodPrimePair (nodeMomentNorm 6 4 1 0) (nodeMomentNorm 6 4 2 0) 120 120 :=
  goodPrimePair_of_samples FixedReplay.N6K4J1W0.candidate FixedReplay.N6K4J2W0.candidate [11, 442, 746, 738, 601, 32, 333, 854, 660, 721, 829, 418, 355, 942, 576, 29, 672, 236, 448, 817, 352, 649, 73, 907, 370, 957, 983, 991, 854, 118, 440, 208, 289, 849, 12, 221, 380, 255, 372, 901, 899, 559, 916, 498, 21, 797, 915, 6, 481, 778, 131, 65, 944, 694, 754, 484, 492, 978, 739, 562, 113, 726, 78, 177, 961, 483, 160, 692, 658, 357, 568, 975, 53, 150, 142, 550, 132, 267, 10, 936, 208, 325, 551, 73, 411, 435, 227, 317, 109, 541, 911, 621, 18, 117, 619, 683, 462, 880, 400, 613, 98, 149, 640, 570, 171, 853, 674, 189, 780, 433, 4, 816, 386, 536, 330, 781, 490, 975, 837, 631] [6, 16, 523, 577, 993, 733, 163, 649, 713, 382, 124, 436, 741, 191, 295, 344, 377, 858, 402, 348, 242, 378, 908, 186, 859, 710, 929, 518, 390, 344, 508, 616, 598, 374, 564, 431, 277, 91, 16, 460, 69, 524, 831, 297, 897, 511, 329, 633, 881, 222, 615, 202, 842, 172, 256, 578, 143, 633, 645, 898, 506, 62, 41, 242, 586, 624, 938, 1005, 78, 523, 114, 632, 267, 325, 890, 516, 548, 225, 861, 102, 679, 256, 155, 337, 210, 60, 304, 391, 845, 257, 918, 941, 197, 644, 370, 432, 629, 794, 777, 783, 273, 106, 185, 981, 459, 654, 406, 244, 271, 651, 474, 388, 925, 161, 475, 668, 48, 858, 144, 157]
    FixedReplay.N6K4J1W0.exactReduction FixedReplay.N6K4J2W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
