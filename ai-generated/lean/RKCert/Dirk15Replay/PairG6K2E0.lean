module
public import RKCert.Dirk15Replay.T6K2J1W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem G6K2E0 : Order15GoodPrimePair (parameterGramNorm 6 2 1 0) (minusParameter (parameterGramNorm 6 2 1 0)) 120 120 :=
  goodPrimePair_of_samples FixedReplay.T6K2J1W0.candidate (alternateResidue true FixedReplay.T6K2J1W0.candidate) [562, 879, 164, 538, 800, 262, 229, 779, 715, 20, 772, 59, 433, 497, 69, 357, 296, 77, 800, 355, 637, 737, 857, 918, 511, 165, 548, 727, 190, 341, 103, 790, 401, 647, 593, 257, 925, 690, 406, 119, 169, 954, 375, 854, 586, 856, 233, 572, 868, 229, 917, 776, 86, 148, 184, 498, 239, 912, 692, 334, 235, 124, 190, 750, 295, 675, 216, 360, 494, 255, 985, 590, 18, 297, 220, 422, 172, 853, 541, 815, 258, 559, 185, 950, 401, 325, 627, 721, 595, 787, 643, 106, 60, 419, 366, 46, 948, 623, 389, 492, 380, 616, 796, 708, 634, 150, 623, 287, 366, 654, 234, 945, 607, 967, 196, 584, 435, 775, 721, 944] [562, 130, 164, 471, 800, 747, 229, 230, 715, 989, 772, 950, 433, 512, 69, 652, 296, 932, 800, 654, 637, 272, 857, 91, 511, 844, 548, 282, 190, 668, 103, 219, 401, 362, 593, 752, 925, 319, 406, 890, 169, 55, 375, 155, 586, 153, 233, 437, 868, 780, 917, 233, 86, 861, 184, 511, 239, 97, 692, 675, 235, 885, 190, 259, 295, 334, 216, 649, 494, 754, 985, 419, 18, 712, 220, 587, 172, 156, 541, 194, 258, 450, 185, 59, 401, 684, 627, 288, 595, 222, 643, 903, 60, 590, 366, 963, 948, 386, 389, 517, 380, 393, 796, 301, 634, 859, 623, 722, 366, 355, 234, 64, 607, 42, 196, 425, 435, 234, 721, 65]
    FixedReplay.T6K2J1W0.exactReduction (minusParameter_reduction FixedReplay.T6K2J1W0.exactReduction)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
