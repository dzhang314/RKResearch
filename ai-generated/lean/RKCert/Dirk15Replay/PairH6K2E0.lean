module
public import RKCert.Dirk15Replay.T6K2J1W0
public import RKCert.Dirk15Replay.H6K2J1W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem H6K2E0 : Order15GoodPrimePair (parameterGramNorm 6 2 1 0) (minusParameter (anchorGramNorm 6 2)) 120 12 :=
  goodPrimePair_of_samples FixedReplay.T6K2J1W0.candidate (alternateResidue true FixedReplay.H6K2J1W0.candidate) [253, 943, 626, 884, 33, 985, 516, 813, 785, 75, 268, 855] [326, 957, 527, 902, 303, 359, 431, 294, 619, 350, 867, 441, 670, 467, 298, 4, 865, 967, 638, 660, 52, 430, 205, 480, 582, 121, 513, 925, 360, 211, 887, 174, 822, 852, 917, 805, 89, 411, 196, 759, 494, 502, 507, 928, 594, 762, 83, 634, 169, 514, 459, 212, 0, 303, 311, 76, 513, 837, 302, 581, 349, 135, 960, 2, 1003, 276, 232, 420, 524, 164, 576, 175, 415, 593, 292, 613, 767, 656, 793, 279, 852, 99, 265, 565, 454, 679, 881, 665, 931, 840, 109, 653, 816, 736, 973, 104, 67, 156, 412, 694, 443, 921, 90, 362, 144, 740, 413, 830, 267, 502, 842, 298, 433, 83, 496, 548, 119, 480, 549, 691]
    FixedReplay.T6K2J1W0.exactReduction (minusParameter_reduction FixedReplay.H6K2J1W0.exactReduction)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
