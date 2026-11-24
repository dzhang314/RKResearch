module
public import RKCert.Dirk15Replay.N6K2J2W0
public import RKCert.Dirk15Replay.N6K2J3W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem F6K2E1 : Order15GoodPrimePair (nodeMomentNorm 6 2 2 0) (nodeMomentNorm 6 2 3 0) 60 60 :=
  goodPrimePair_of_samples FixedReplay.N6K2J2W0.candidate FixedReplay.N6K2J3W0.candidate [546, 623, 768, 649, 410, 791, 946, 678, 360, 796, 117, 866, 801, 779, 4, 414, 698, 615, 126, 48, 29, 279, 242, 378, 774, 719, 925, 148, 533, 619, 622, 353, 6, 593, 961, 929, 556, 133, 753, 353, 1, 735, 96, 321, 124, 931, 126, 850, 148, 413, 284, 151, 614, 67, 312, 570, 284, 446, 961, 851] [706, 1005, 448, 145, 115, 346, 268, 663, 620, 336, 618, 893, 564, 469, 265, 497, 1005, 251, 436, 146, 335, 991, 653, 79, 433, 408, 562, 696, 844, 631, 9, 563, 287, 980, 756, 571, 546, 136, 1000, 306, 617, 724, 973, 302, 292, 79, 186, 677, 421, 490, 881, 478, 720, 916, 781, 487, 469, 229, 590, 66]
    FixedReplay.N6K2J2W0.exactReduction FixedReplay.N6K2J3W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
