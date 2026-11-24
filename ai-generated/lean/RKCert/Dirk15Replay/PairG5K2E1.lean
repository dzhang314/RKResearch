module
public import RKCert.Dirk15Replay.T5K2J2W0
public import RKCert.Dirk15Replay.T5K2J1W1

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem G5K2E1 : Order15GoodPrimePair (parameterGramNorm 5 2 2 0) (minusParameter (parameterGramNorm 5 2 1 1)) 80 100 :=
  goodPrimePair_of_samples FixedReplay.T5K2J2W0.candidate (alternateResidue true FixedReplay.T5K2J1W1.candidate) [139, 630, 920, 966, 610, 299, 174, 457, 967, 294, 222, 384, 124, 804, 444, 205, 595, 566, 339, 733, 348, 813, 421, 297, 774, 969, 749, 79, 1005, 810, 499, 730, 377, 749, 891, 603, 76, 267, 814, 704, 465, 851, 922, 126, 463, 690, 2, 995, 758, 417, 180, 159, 640, 707, 716, 702, 613, 508, 667, 775, 164, 156, 556, 745, 424, 303, 987, 632, 16, 73, 991, 202, 214, 672, 701, 1007, 801, 903, 725, 693, 473, 536, 332, 323, 616, 609, 507, 682, 376, 722, 949, 646, 393, 133, 208, 555, 307, 241, 753, 115] [350, 204, 429, 624, 93, 441, 150, 310, 131, 150, 468, 812, 415, 637, 349, 448, 290, 19, 650, 305, 462, 392, 948, 845, 788, 659, 999, 633, 384, 889, 645, 511, 246, 679, 645, 869, 695, 301, 879, 479, 758, 457, 875, 177, 949, 814, 486, 815, 579, 122, 411, 878, 793, 995, 184, 340, 203, 104, 19, 261, 152, 708, 137, 363, 772, 734, 315, 176, 89, 59, 965, 626, 799, 111, 600, 416, 939, 599, 844, 692]
    FixedReplay.T5K2J2W0.exactReduction (minusParameter_reduction FixedReplay.T5K2J1W1.exactReduction)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
