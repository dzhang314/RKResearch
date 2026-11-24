module
public import RKCert.Dirk15Replay.T6K2J2W0
public import RKCert.Dirk15Replay.T6K2J1W1

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem G6K2E1 : Order15GoodPrimePair (parameterGramNorm 6 2 2 0) (minusParameter (parameterGramNorm 6 2 1 1)) 120 150 :=
  goodPrimePair_of_samples FixedReplay.T6K2J2W0.candidate (alternateResidue true FixedReplay.T6K2J1W1.candidate) [720, 602, 705, 344, 124, 271, 377, 652, 914, 283, 529, 900, 739, 963, 126, 618, 780, 3, 482, 477, 481, 890, 682, 976, 550, 597, 16, 972, 327, 370, 101, 935, 977, 440, 409, 476, 107, 611, 972, 595, 0, 273, 808, 808, 842, 854, 99, 4, 962, 310, 282, 702, 598, 752, 262, 16, 427, 873, 225, 949, 732, 818, 150, 585, 652, 770, 540, 163, 833, 645, 591, 520, 208, 16, 703, 692, 683, 169, 184, 467, 422, 386, 835, 884, 607, 555, 450, 669, 982, 102, 112, 422, 692, 462, 511, 105, 358, 652, 475, 120, 775, 759, 345, 942, 297, 83, 924, 809, 427, 526, 205, 618, 438, 509, 183, 38, 293, 166, 322, 361, 282, 962, 354, 37, 534, 700, 37, 543, 755, 438, 629, 374, 610, 158, 512, 874, 311, 13, 41, 721, 178, 966, 1005, 185, 55, 1002, 187, 420, 865, 189] [878, 35, 934, 407, 905, 419, 811, 972, 238, 297, 81, 439, 274, 222, 623, 177, 753, 259, 817, 507, 913, 317, 907, 137, 760, 231, 410, 873, 369, 355, 913, 119, 153, 305, 323, 156, 79, 451, 532, 468, 554, 623, 618, 893, 973, 679, 803, 944, 342, 71, 344, 759, 303, 607, 48, 330, 433, 893, 18, 479, 52, 108, 942, 747, 49, 200, 907, 846, 298, 668, 449, 732, 622, 93, 465, 630, 13, 167, 850, 911, 924, 569, 164, 967, 310, 993, 115, 68, 562, 710, 126, 794, 178, 321, 221, 975, 139, 207, 800, 992, 916, 392, 701, 445, 119, 616, 218, 351, 758, 613, 16, 389, 577, 473, 507, 800, 252, 866, 730, 577]
    FixedReplay.T6K2J2W0.exactReduction (minusParameter_reduction FixedReplay.T6K2J1W1.exactReduction)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.FixedReplay
