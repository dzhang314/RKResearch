module
public import RKCert.Dirk15Replay.N5K3J2W0
public import RKCert.Dirk15Replay.N5K3J3W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem F5K3E1 : Order15GoodPrimePair (nodeMomentNorm 5 3 2 0) (nodeMomentNorm 5 3 3 0) 60 60 :=
  goodPrimePair_of_samples FixedReplay.N5K3J2W0.candidate FixedReplay.N5K3J3W0.candidate [70, 152, 906, 136, 458, 287, 343, 879, 924, 30, 782, 109, 648, 633, 180, 799, 710, 855, 651, 87, 435, 387, 380, 935, 520, 755, 571, 313, 287, 634, 797, 25, 610, 511, 142, 823, 279, 540, 400, 242, 426, 4, 509, 991, 726, 757, 422, 597, 382, 931, 338, 78, 236, 1003, 189, 681, 855, 442, 337, 844] [583, 367, 506, 987, 179, 1002, 147, 589, 312, 487, 406, 999, 335, 293, 198, 368, 656, 747, 727, 949, 210, 938, 933, 272, 932, 187, 499, 871, 729, 621, 963, 36, 477, 14, 605, 237, 442, 45, 229, 263, 13, 898, 39, 531, 198, 867, 372, 123, 243, 559, 647, 578, 472, 158, 504, 272, 839, 197, 658, 387]
    FixedReplay.N5K3J2W0.exactReduction FixedReplay.N5K3J3W0.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
