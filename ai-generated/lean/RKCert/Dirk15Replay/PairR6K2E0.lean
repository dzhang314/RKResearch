module
public import RKCert.Dirk15Replay.N6K2J1W1
public import RKCert.Dirk15Replay.N6K2J2W1

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem R6K2E0 : Order15GoodPrimePair (nodeMomentNorm 6 2 1 1) (nodeMomentNorm 6 2 2 1) 75 75 :=
  goodPrimePair_of_samples FixedReplay.N6K2J1W1.candidate FixedReplay.N6K2J2W1.candidate [307, 542, 78, 0, 864, 280, 451, 402, 431, 726, 214, 511, 545, 153, 403, 989, 17, 394, 109, 531, 145, 843, 128, 869, 877, 460, 299, 45, 821, 401, 235, 363, 780, 296, 312, 745, 88, 132, 970, 1007, 997, 884, 949, 674, 959, 364, 767, 208, 518, 796, 297, 522, 606, 729, 314, 737, 354, 858, 369, 512, 358, 677, 202, 934, 865, 654, 644, 58, 710, 483, 641, 992, 934, 645, 914] [808, 500, 39, 628, 132, 972, 728, 321, 175, 912, 795, 560, 87, 643, 221, 477, 784, 984, 723, 89, 106, 494, 620, 312, 589, 746, 207, 686, 703, 978, 150, 733, 685, 137, 193, 254, 144, 480, 895, 241, 699, 1008, 968, 207, 322, 117, 723, 487, 25, 484, 662, 839, 228, 347, 330, 896, 944, 576, 682, 767, 931, 358, 394, 929, 625, 10, 863, 997, 53, 618, 223, 477, 939, 150, 78]
    FixedReplay.N6K2J1W1.exactReduction FixedReplay.N6K2J2W1.exactReduction
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
