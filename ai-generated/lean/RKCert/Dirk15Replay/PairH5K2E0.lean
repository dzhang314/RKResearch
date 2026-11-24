module
public import RKCert.Dirk15Replay.T5K2J1W0
public import RKCert.Dirk15Replay.H5K2J1W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem H5K2E0 : Order15GoodPrimePair (parameterGramNorm 5 2 1 0) (minusParameter (anchorGramNorm 5 2)) 80 10 :=
  goodPrimePair_of_samples FixedReplay.T5K2J1W0.candidate (alternateResidue true FixedReplay.H5K2J1W0.candidate) [897, 669, 840, 192, 491, 787, 934, 947, 752, 978] [1008, 794, 629, 291, 560, 603, 832, 166, 416, 213, 212, 819, 183, 979, 358, 472, 31, 672, 689, 247, 264, 285, 606, 312, 564, 450, 305, 860, 846, 126, 785, 26, 956, 114, 780, 267, 166, 19, 21, 950, 757, 772, 310, 574, 625, 925, 919, 625, 139, 388, 1, 301, 544, 802, 619, 194, 444, 127, 107, 406, 183, 496, 586, 563, 813, 522, 403, 361, 642, 583, 699, 152, 232, 356, 716, 305, 534, 535, 968, 888]
    FixedReplay.T5K2J1W0.exactReduction (minusParameter_reduction FixedReplay.H5K2J1W0.exactReduction)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
