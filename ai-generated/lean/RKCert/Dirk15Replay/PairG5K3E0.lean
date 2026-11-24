module
public import RKCert.Dirk15Replay.T5K3J1W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem G5K3E0 : Order15GoodPrimePair (parameterGramNorm 5 3 1 0) (minusParameter (parameterGramNorm 5 3 1 0)) 120 120 :=
  goodPrimePair_of_samples FixedReplay.T5K3J1W0.candidate (alternateResidue true FixedReplay.T5K3J1W0.candidate) [611, 609, 451, 853, 471, 638, 623, 294, 147, 9, 592, 806, 254, 452, 562, 164, 111, 807, 397, 135, 694, 889, 451, 2, 453, 269, 954, 183, 92, 863, 740, 748, 481, 920, 317, 392, 309, 674, 818, 25, 872, 72, 14, 381, 326, 878, 585, 878, 632, 877, 320, 389, 117, 643, 614, 276, 449, 70, 55, 711, 155, 717, 238, 786, 222, 465, 588, 826, 522, 383, 301, 717, 705, 112, 796, 269, 728, 251, 259, 100, 863, 996, 49, 198, 421, 81, 452, 370, 418, 579, 564, 615, 70, 337, 808, 891, 812, 825, 209, 287, 778, 668, 1006, 281, 373, 876, 275, 530, 509, 125, 535, 783, 468, 870, 551, 37, 629, 226, 902, 911] [611, 400, 451, 156, 471, 371, 623, 715, 147, 1000, 592, 203, 254, 557, 562, 845, 111, 202, 397, 874, 694, 120, 451, 1007, 453, 740, 954, 826, 92, 146, 740, 261, 481, 89, 317, 617, 309, 335, 818, 984, 872, 937, 14, 628, 326, 131, 585, 131, 632, 132, 320, 620, 117, 366, 614, 733, 449, 939, 55, 298, 155, 292, 238, 223, 222, 544, 588, 183, 522, 626, 301, 292, 705, 897, 796, 740, 728, 758, 259, 909, 863, 13, 49, 811, 421, 928, 452, 639, 418, 430, 564, 394, 70, 672, 808, 118, 812, 184, 209, 722, 778, 341, 1006, 728, 373, 133, 275, 479, 509, 884, 535, 226, 468, 139, 551, 972, 629, 783, 902, 98]
    FixedReplay.T5K3J1W0.exactReduction (minusParameter_reduction FixedReplay.T5K3J1W0.exactReduction)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
