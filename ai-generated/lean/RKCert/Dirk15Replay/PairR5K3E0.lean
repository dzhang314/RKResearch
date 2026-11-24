module
public import RKCert.Dirk15Replay.N5K3J1W1
public import RKCert.Dirk15Replay.N5K3J2W1

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem R5K3E0 : Order15GoodPrimePair (nodeMomentNorm 5 3 1 1) (nodeMomentNorm 5 3 2 1) 70 70 :=
  goodPrimePair_of_samples FixedReplay.N5K3J1W1.candidate FixedReplay.N5K3J2W1.candidate [2, 737, 750, 847, 761, 140, 110, 880, 564, 181, 766, 235, 19, 775, 739, 991, 158, 972, 74, 666, 591, 181, 857, 158, 48, 197, 720, 341, 230, 906, 392, 379, 508, 740, 146, 740, 634, 666, 850, 107, 130, 588, 737, 941, 894, 517, 134, 801, 739, 913, 740, 191, 781, 294, 938, 526, 862, 565, 777, 810, 569, 457, 659, 126, 760, 0, 881, 369, 963, 960] [428, 868, 167, 208, 715, 398, 401, 12, 451, 405, 1007, 583, 387, 789, 893, 184, 898, 803, 723, 198, 729, 451, 578, 330, 781, 360, 848, 289, 815, 854, 1006, 754, 860, 585, 316, 220, 72, 218, 570, 314, 87, 279, 88, 394, 397, 437, 460, 809, 707, 809, 948, 678, 55, 60, 600, 275, 182, 458, 388, 109, 900, 576, 612, 162, 235, 382, 285, 487, 590, 225]
    FixedReplay.N5K3J1W1.exactReduction FixedReplay.N5K3J2W1.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
