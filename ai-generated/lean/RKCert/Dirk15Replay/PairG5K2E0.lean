module
public import RKCert.Dirk15Replay.T5K2J1W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem G5K2E0 : Order15GoodPrimePair (parameterGramNorm 5 2 1 0) (minusParameter (parameterGramNorm 5 2 1 0)) 80 80 :=
  goodPrimePair_of_samples FixedReplay.T5K2J1W0.candidate (alternateResidue true FixedReplay.T5K2J1W0.candidate) [1007, 111, 913, 111, 320, 718, 685, 602, 910, 746, 987, 145, 728, 738, 963, 224, 243, 277, 972, 813, 757, 778, 730, 93, 781, 1000, 781, 527, 13, 835, 537, 86, 432, 539, 979, 992, 725, 150, 269, 184, 140, 326, 114, 732, 801, 423, 11, 632, 791, 198, 9, 729, 705, 794, 868, 446, 877, 509, 926, 330, 686, 133, 438, 451, 82, 352, 2, 887, 334, 231, 261, 441, 202, 562, 51, 349, 598, 954, 624, 945] [1007, 898, 913, 898, 320, 291, 685, 407, 910, 263, 987, 864, 728, 271, 963, 785, 243, 732, 972, 196, 757, 231, 730, 916, 781, 9, 781, 482, 13, 174, 537, 923, 432, 470, 979, 17, 725, 859, 269, 825, 140, 683, 114, 277, 801, 586, 11, 377, 791, 811, 9, 280, 705, 215, 868, 563, 877, 500, 926, 679, 686, 876, 438, 558, 82, 657, 2, 122, 334, 778, 261, 568, 202, 447, 51, 660, 598, 55, 624, 64]
    FixedReplay.T5K2J1W0.exactReduction (minusParameter_reduction FixedReplay.T5K2J1W0.exactReduction)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
