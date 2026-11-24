module
public import RKCert.Dirk15Replay.T5K3J1W0
public import RKCert.Dirk15Replay.H5K3J1W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem H5K3E0 : Order15GoodPrimePair (parameterGramNorm 5 3 1 0) (minusParameter (anchorGramNorm 5 3)) 120 20 :=
  goodPrimePair_of_samples FixedReplay.T5K3J1W0.candidate (alternateResidue true FixedReplay.H5K3J1W0.candidate) [439, 181, 304, 262, 434, 81, 896, 891, 710, 320, 146, 16, 194, 291, 486, 731, 546, 24, 900, 653] [577, 563, 621, 292, 357, 933, 63, 307, 920, 334, 326, 952, 964, 428, 888, 519, 436, 981, 24, 936, 56, 842, 896, 838, 863, 616, 914, 439, 419, 712, 882, 812, 510, 993, 717, 136, 856, 35, 584, 156, 568, 415, 648, 425, 300, 96, 595, 277, 541, 862, 905, 539, 462, 576, 819, 101, 144, 71, 218, 324, 379, 76, 133, 408, 336, 294, 427, 154, 775, 990, 513, 154, 430, 846, 445, 320, 73, 998, 259, 176, 74, 867, 391, 940, 561, 79, 39, 324, 460, 257, 113, 621, 226, 587, 9, 992, 171, 169, 927, 109, 511, 674, 758, 476, 268, 145, 49, 786, 802, 704, 792, 244, 376, 38, 535, 609, 166, 875, 831, 467]
    FixedReplay.T5K3J1W0.exactReduction (minusParameter_reduction FixedReplay.H5K3J1W0.exactReduction)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
