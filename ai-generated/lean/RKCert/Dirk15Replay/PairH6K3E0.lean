module
public import RKCert.Dirk15Replay.T6K3J1W0
public import RKCert.Dirk15Replay.H6K3J1W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem H6K3E0 : Order15GoodPrimePair (parameterGramNorm 6 3 1 0) (minusParameter (anchorGramNorm 6 3)) 240 30 :=
  goodPrimePair_of_samples FixedReplay.T6K3J1W0.candidate (alternateResidue true FixedReplay.H6K3J1W0.candidate) [241, 227, 455, 6, 845, 790, 759, 639, 366, 42, 396, 736, 652, 863, 1004, 439, 69, 25, 211, 707, 236, 882, 807, 109, 983, 622, 949, 653, 103, 54] [322, 489, 568, 882, 923, 167, 632, 84, 860, 320, 690, 918, 390, 239, 331, 496, 256, 745, 218, 889, 39, 984, 662, 179, 921, 994, 144, 761, 110, 356, 623, 852, 592, 70, 217, 431, 959, 943, 530, 719, 729, 540, 551, 977, 111, 651, 310, 329, 493, 456, 851, 629, 26, 98, 907, 253, 587, 126, 190, 605, 857, 113, 120, 658, 27, 436, 739, 553, 739, 236, 487, 852, 277, 292, 720, 357, 545, 816, 749, 268, 490, 62, 258, 494, 390, 628, 468, 453, 718, 345, 400, 446, 99, 307, 303, 265, 730, 215, 482, 490, 560, 486, 459, 480, 292, 547, 323, 69, 714, 408, 37, 14, 878, 410, 326, 760, 134, 738, 460, 706, 726, 693, 236, 689, 894, 135, 859, 65, 753, 271, 622, 160, 835, 312, 421, 283, 866, 409, 34, 990, 825, 541, 104, 920, 938, 4, 479, 422, 274, 567, 858, 968, 652, 379, 212, 12, 122, 149, 939, 985, 194, 314, 438, 670, 722, 584, 594, 595, 193, 172, 902, 613, 310, 903, 70, 196, 367, 601, 730, 57, 401, 281, 924, 423, 372, 132, 908, 831, 611, 291, 815, 874, 48, 282, 708, 716, 937, 9, 763, 615, 530, 594, 211, 43, 35, 130, 944, 414, 414, 956, 319, 696, 1007, 592, 969, 50, 543, 163, 765, 243, 334, 673, 375, 796, 141, 439, 169, 58, 650, 755, 992, 756, 116, 820, 492, 130, 546, 0, 763, 54]
    FixedReplay.T6K3J1W0.exactReduction (minusParameter_reduction FixedReplay.H6K3J1W0.exactReduction)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
