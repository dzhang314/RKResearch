import Lean

namespace RKResearch.Certified.Graded.OrderTwelveFifteen.RadauPencilArithmetic

set_option maxRecDepth 20000
set_option maxHeartbeats 0

def J5 : List Int := [-1, 35, -280, 840, -1050, 462]
def J6 : List Int := [1, -48, 540, -2400, 4950, -4752, 1716]

def clearedMoment (f : List Int) (j : Nat) : Int :=
  (((List.range f.length).map fun i => (f[i]?.getD 0) *
    Int.ofNat (360360 / ((i+j+1)*(i+j+2)))).foldl (· + ·) 0)

theorem J5_moments : (List.range 5).map (clearedMoment J5) = [0,0,0,0,0] := by decide
theorem J6_moments : (List.range 6).map (clearedMoment J6) = [0,0,0,0,0,0] := by decide

/-- The only possible proper prime divisors of 1009 would be at most 31. -/
theorem certifyPrime : ((List.range 30).map (· + 2)).all (fun q => 1009 % q != 0) = true := by decide

def addMod (p : Nat) (x y : List Nat) : List Nat :=
  match x, y with
  | [], ys => ys
  | xs, [] => xs
  | a::as, b::bs => ((a+b)%p)::addMod p as bs

def mulMod (p : Nat) (f g : List Nat) : List Nat :=
  match f with
  | [] => []
  | a::as => addMod p (g.map (fun b => a*b%p)) (0::mulMod p as g)

def normalize (f : List Nat) : List Nat :=
  (f.reverse.dropWhile (· == 0)).reverse

def pays (p : Nat) (f g q r : List Nat) : Bool :=
  g.getLastD 0 % p != 0 && r.length < g.length && normalize r == r &&
  normalize (addMod p (mulMod p q g) r) == f

/-- Linked decreasing polynomial remainder identities ending at a nonzero constant. -/
inductive CheckedEuclid (p : Nat) : List Nat → List Nat → Prop where
  | done (f : List Nat) : f.length = 1 → f.headD 0 % p ≠ 0 → CheckedEuclid p f []
  | step {f g q r : List Nat} :
      pays p f g q r = true → CheckedEuclid p g r → CheckedEuclid p f g

namespace Pair0

def p0 : List Nat := [309, 253, 271, 617, 210, 198, 301, 833, 391, 561, 10, 931, 269, 172, 443, 581, 273, 970, 606, 124, 98, 1006, 117, 820, 90, 426, 171, 6, 521, 41, 390, 764, 277, 92, 182, 281, 407, 47, 400, 217, 164]
def p1 : List Nat := [626, 953, 470, 901, 586, 131, 728, 233, 989, 270, 184, 705, 202, 364, 573, 709, 167, 766, 4, 437, 115, 636, 968, 983, 952, 697, 152, 82, 921, 979, 536, 589, 388, 66, 924, 231, 785, 288, 313, 814, 420]
def p2 : List Nat := [103, 813, 616, 688, 404, 906, 84, 521, 591, 888, 188, 944, 267, 568, 767, 554, 621, 373, 566, 799, 966, 700, 527, 71, 660, 519, 669, 195, 392, 341, 75, 928, 433, 441, 23, 998, 629, 194, 297, 149]
def p3 : List Nat := [824, 216, 120, 472, 239, 670, 995, 452, 231, 239, 587, 501, 676, 213, 305, 280, 410, 534, 809, 366, 916, 21, 887, 161, 198, 107, 757, 733, 127, 226, 302, 618, 727, 465, 291, 851, 256, 81, 467]
def p4 : List Nat := [295, 221, 32, 15, 85, 180, 30, 982, 399, 311, 99, 21, 222, 59, 867, 459, 519, 917, 477, 968, 850, 853, 352, 202, 451, 574, 851, 283, 274, 290, 669, 671, 248, 28, 36, 706, 538, 313]
def p5 : List Nat := [919, 229, 913, 550, 624, 537, 388, 560, 92, 429, 127, 833, 547, 668, 275, 303, 165, 52, 143, 233, 64, 62, 975, 877, 291, 926, 100, 791, 213, 342, 722, 93, 484, 481, 326, 312, 405]
def p6 : List Nat := [449, 392, 246, 613, 381, 42, 558, 997, 180, 34, 888, 802, 299, 723, 655, 17, 578, 125, 516, 688, 969, 827, 726, 63, 511, 95, 754, 215, 514, 26, 111, 639, 342, 388, 387, 695]
def p7 : List Nat := [289, 931, 553, 952, 239, 531, 416, 254, 610, 23, 148, 334, 524, 515, 165, 170, 74, 89, 422, 53, 765, 993, 691, 905, 723, 883, 931, 422, 646, 647, 878, 416, 843, 250, 440]
def p8 : List Nat := [40, 677, 818, 968, 956, 59, 974, 434, 547, 389, 113, 30, 489, 414, 220, 918, 72, 813, 1006, 627, 7, 18, 99, 415, 669, 904, 353, 728, 127, 859, 555, 977, 129, 847]
def p9 : List Nat := [864, 272, 65, 434, 722, 835, 847, 434, 233, 936, 445, 795, 44, 666, 472, 171, 239, 438, 882, 673, 630, 950, 131, 567, 108, 859, 820, 535, 729, 944, 998, 716, 239]
def p10 : List Nat := [461, 949, 504, 604, 701, 753, 237, 123, 835, 311, 282, 525, 773, 665, 452, 892, 857, 761, 938, 346, 369, 597, 200, 148, 412, 839, 695, 355, 850, 357, 505, 657]
def p11 : List Nat := [951, 834, 954, 646, 269, 255, 933, 111, 375, 64, 525, 11, 818, 609, 825, 173, 862, 762, 53, 830, 18, 147, 380, 338, 726, 550, 937, 638, 838, 767, 153]
def p12 : List Nat := [435, 698, 537, 526, 1005, 625, 778, 231, 989, 72, 439, 183, 239, 215, 720, 151, 214, 952, 864, 601, 544, 954, 173, 565, 776, 336, 233, 416, 723, 684]
def p13 : List Nat := [486, 78, 873, 19, 618, 128, 971, 808, 705, 431, 719, 343, 197, 545, 406, 312, 317, 613, 473, 388, 317, 899, 781, 95, 254, 953, 849, 127, 190]
def p14 : List Nat := [728, 271, 1003, 202, 208, 938, 330, 786, 806, 607, 557, 676, 531, 926, 618, 751, 386, 454, 176, 127, 846, 126, 444, 143, 529, 14, 138, 535]
def p15 : List Nat := [324, 946, 371, 244, 958, 590, 153, 566, 588, 947, 395, 116, 608, 656, 718, 1005, 995, 531, 304, 710, 527, 906, 596, 508, 455, 420, 11]
def p16 : List Nat := [44, 56, 848, 559, 801, 532, 756, 660, 900, 779, 425, 829, 954, 495, 453, 63, 233, 656, 85, 58, 802, 39, 567, 710, 555, 694]
def p17 : List Nat := [652, 842, 300, 557, 938, 650, 326, 871, 576, 666, 285, 692, 480, 228, 430, 609, 551, 375, 393, 627, 6, 723, 533, 482, 881]
def p18 : List Nat := [22, 844, 60, 909, 368, 751, 517, 166, 709, 933, 579, 2, 593, 4, 786, 924, 384, 176, 159, 319, 148, 712, 490, 406]
def p19 : List Nat := [744, 989, 465, 587, 140, 730, 836, 275, 592, 217, 90, 760, 651, 837, 200, 988, 253, 402, 324, 351, 791, 984, 226]
def p20 : List Nat := [164, 94, 428, 594, 65, 761, 380, 988, 486, 562, 907, 606, 448, 193, 694, 235, 312, 886, 762, 139, 641, 618]
def p21 : List Nat := [387, 761, 611, 362, 590, 345, 657, 532, 850, 203, 802, 385, 483, 454, 570, 337, 410, 563, 790, 953, 604]
def p22 : List Nat := [990, 65, 762, 869, 807, 769, 30, 439, 93, 834, 63, 94, 728, 391, 451, 145, 656, 571, 254, 760]
def p23 : List Nat := [230, 352, 616, 129, 997, 551, 777, 259, 319, 632, 373, 724, 30, 621, 635, 959, 219, 161, 40]
def p24 : List Nat := [218, 199, 947, 103, 37, 411, 535, 433, 515, 750, 464, 895, 427, 360, 515, 970, 441, 511]
def p25 : List Nat := [191, 650, 702, 872, 918, 248, 441, 242, 5, 409, 318, 644, 313, 283, 615, 169, 70]
def p26 : List Nat := [546, 25, 107, 477, 501, 87, 399, 623, 196, 45, 7, 660, 742, 157, 837, 186]
def p27 : List Nat := [229, 258, 386, 208, 969, 974, 754, 787, 673, 555, 491, 758, 506, 919, 486]
def p28 : List Nat := [328, 809, 46, 360, 805, 139, 516, 428, 835, 494, 806, 921, 298, 814]
def p29 : List Nat := [828, 332, 645, 447, 957, 1002, 502, 172, 304, 117, 412, 657, 636]
def p30 : List Nat := [73, 552, 679, 865, 166, 93, 497, 49, 942, 940, 580, 738]
def p31 : List Nat := [704, 647, 655, 116, 788, 575, 85, 965, 314, 188, 591]
def p32 : List Nat := [18, 557, 663, 434, 563, 751, 840, 688, 712, 54]
def p33 : List Nat := [735, 120, 970, 390, 315, 79, 992, 468, 625]
def p34 : List Nat := [584, 663, 290, 780, 946, 629, 380, 461]
def p35 : List Nat := [20, 972, 554, 448, 163, 573, 477]
def p36 : List Nat := [438, 452, 854, 761, 139, 582]
def p37 : List Nat := [613, 393, 592, 412, 459]
def p38 : List Nat := [517, 833, 219, 644]
def p39 : List Nat := [989, 647, 348]
def p40 : List Nat := [669, 854]
def p41 : List Nat := [840]
def p42 : List Nat := []

private theorem tail41 : CheckedEuclid 1009 p41 p42 :=
  CheckedEuclid.done p41 (by decide) (by decide)
private theorem tail40 : CheckedEuclid 1009 p40 p41 :=
  CheckedEuclid.step (q := [408, 186]) (r := p42)
    (by decide_cbv) tail41
private theorem tail39 : CheckedEuclid 1009 p39 p40 :=
  CheckedEuclid.step (q := [418, 499]) (r := p41)
    (by decide_cbv) tail40
private theorem tail38 : CheckedEuclid 1009 p38 p39 :=
  CheckedEuclid.step (q := [613, 257]) (r := p40)
    (by decide_cbv) tail39
private theorem tail37 : CheckedEuclid 1009 p37 p38 :=
  CheckedEuclid.step (q := [91, 817]) (r := p39)
    (by decide_cbv) tail38
private theorem tail36 : CheckedEuclid 1009 p36 p37 :=
  CheckedEuclid.step (q := [441, 87]) (r := p38)
    (by decide_cbv) tail37
private theorem tail35 : CheckedEuclid 1009 p35 p36 :=
  CheckedEuclid.step (q := [411, 911]) (r := p37)
    (by decide_cbv) tail36
private theorem tail34 : CheckedEuclid 1009 p34 p35 :=
  CheckedEuclid.step (q := [310, 130]) (r := p36)
    (by decide_cbv) tail35
private theorem tail33 : CheckedEuclid 1009 p33 p34 :=
  CheckedEuclid.step (q := [853, 148]) (r := p35)
    (by decide_cbv) tail34
private theorem tail32 : CheckedEuclid 1009 p32 p33 :=
  CheckedEuclid.step (q := [142, 394]) (r := p34)
    (by decide_cbv) tail33
private theorem tail31 : CheckedEuclid 1009 p31 p32 :=
  CheckedEuclid.step (q := [727, 67]) (r := p33)
    (by decide_cbv) tail32
private theorem tail30 : CheckedEuclid 1009 p30 p31 :=
  CheckedEuclid.step (q := [678, 201]) (r := p32)
    (by decide_cbv) tail31
private theorem tail29 : CheckedEuclid 1009 p29 p30 :=
  CheckedEuclid.step (q := [444, 854]) (r := p31)
    (by decide_cbv) tail30
private theorem tail28 : CheckedEuclid 1009 p28 p29 :=
  CheckedEuclid.step (q := [216, 785]) (r := p30)
    (by decide_cbv) tail29
private theorem tail27 : CheckedEuclid 1009 p27 p28 :=
  CheckedEuclid.step (q := [758, 665]) (r := p29)
    (by decide_cbv) tail28
private theorem tail26 : CheckedEuclid 1009 p26 p27 :=
  CheckedEuclid.step (q := [468, 399]) (r := p28)
    (by decide_cbv) tail27
private theorem tail25 : CheckedEuclid 1009 p25 p26 :=
  CheckedEuclid.step (q := [303, 532]) (r := p27)
    (by decide_cbv) tail26
private theorem tail24 : CheckedEuclid 1009 p24 p25 :=
  CheckedEuclid.step (q := [1002, 310]) (r := p26)
    (by decide_cbv) tail25
private theorem tail23 : CheckedEuclid 1009 p23 p24 :=
  CheckedEuclid.step (q := [264, 239]) (r := p25)
    (by decide_cbv) tail24
private theorem tail22 : CheckedEuclid 1009 p22 p23 :=
  CheckedEuclid.step (q := [56, 19]) (r := p24)
    (by decide_cbv) tail23
private theorem tail21 : CheckedEuclid 1009 p21 p22 :=
  CheckedEuclid.step (q := [629, 962]) (r := p23)
    (by decide_cbv) tail22
private theorem tail20 : CheckedEuclid 1009 p20 p21 :=
  CheckedEuclid.step (q := [767, 1000]) (r := p22)
    (by decide_cbv) tail21
private theorem tail19 : CheckedEuclid 1009 p19 p20 :=
  CheckedEuclid.step (q := [439, 82]) (r := p21)
    (by decide_cbv) tail20
private theorem tail18 : CheckedEuclid 1009 p18 p19 :=
  CheckedEuclid.step (q := [941, 859]) (r := p20)
    (by decide_cbv) tail19
private theorem tail17 : CheckedEuclid 1009 p17 p18 :=
  CheckedEuclid.step (q := [271, 283]) (r := p19)
    (by decide_cbv) tail18
private theorem tail16 : CheckedEuclid 1009 p16 p17 :=
  CheckedEuclid.step (q := [715, 168]) (r := p18)
    (by decide_cbv) tail17
private theorem tail15 : CheckedEuclid 1009 p15 p16 :=
  CheckedEuclid.step (q := [176, 237]) (r := p17)
    (by decide_cbv) tail16
private theorem tail14 : CheckedEuclid 1009 p14 p15 :=
  CheckedEuclid.step (q := [899, 599]) (r := p16)
    (by decide_cbv) tail15
private theorem tail13 : CheckedEuclid 1009 p13 p14 :=
  CheckedEuclid.step (q := [319, 519]) (r := p15)
    (by decide_cbv) tail14
private theorem tail12 : CheckedEuclid 1009 p12 p13 :=
  CheckedEuclid.step (q := [234, 609]) (r := p14)
    (by decide_cbv) tail13
private theorem tail11 : CheckedEuclid 1009 p11 p12 :=
  CheckedEuclid.step (q := [349, 518]) (r := p13)
    (by decide_cbv) tail12
private theorem tail10 : CheckedEuclid 1009 p10 p11 :=
  CheckedEuclid.step (q := [765, 123]) (r := p12)
    (by decide_cbv) tail11
private theorem tail9 : CheckedEuclid 1009 p9 p10 :=
  CheckedEuclid.step (q := [2, 822]) (r := p11)
    (by decide_cbv) tail10
private theorem tail8 : CheckedEuclid 1009 p8 p9 :=
  CheckedEuclid.step (q := [323, 907]) (r := p10)
    (by decide_cbv) tail9
private theorem tail7 : CheckedEuclid 1009 p7 p8 :=
  CheckedEuclid.step (q := [364, 944]) (r := p9)
    (by decide_cbv) tail8
private theorem tail6 : CheckedEuclid 1009 p6 p7 :=
  CheckedEuclid.step (q := [169, 701]) (r := p8)
    (by decide_cbv) tail7
private theorem tail5 : CheckedEuclid 1009 p5 p6 :=
  CheckedEuclid.step (q := [125, 741]) (r := p7)
    (by decide_cbv) tail6
private theorem tail4 : CheckedEuclid 1009 p4 p5 :=
  CheckedEuclid.step (q := [495, 656]) (r := p6)
    (by decide_cbv) tail5
private theorem tail3 : CheckedEuclid 1009 p3 p4 :=
  CheckedEuclid.step (q := [222, 398]) (r := p5)
    (by decide_cbv) tail4
private theorem tail2 : CheckedEuclid 1009 p2 p3 :=
  CheckedEuclid.step (q := [421, 292]) (r := p4)
    (by decide_cbv) tail3
private theorem tail1 : CheckedEuclid 1009 p1 p2 :=
  CheckedEuclid.step (q := [194, 680]) (r := p3)
    (by decide_cbv) tail2
private theorem tail0 : CheckedEuclid 1009 p0 p1 :=
  CheckedEuclid.step (q := [10]) (r := p2)
    (by decide_cbv) tail1

theorem euclid : CheckedEuclid 1009 p0 p1 := tail0
theorem degreesPreserved : p0.length = 41 ∧ p1.length = 41 ∧
    p0.getLastD 0 % 1009 = 164 ∧ p1.getLastD 0 % 1009 = 420 := by decide

end Pair0

namespace Pair1

def p0 : List Nat := [762, 64, 11, 626, 47, 509, 320, 324, 312, 266, 380, 156, 759, 632, 855, 813, 882, 197, 523, 713, 755, 446, 439, 608, 791, 411, 229, 903, 344, 738, 508, 686, 346, 745, 171, 11, 112, 1008, 905, 28, 182, 141, 257, 124, 773, 958, 387, 341, 874, 61, 573, 849, 336, 210, 706, 413, 635, 922, 339, 716, 162]
def p1 : List Nat := [858, 939, 570, 25, 471, 728, 704, 446, 311, 679, 49, 279, 372, 816, 900, 909, 406, 984, 946, 962, 538, 507, 799, 230, 363, 871, 934, 592, 107, 560, 156, 308, 188, 828, 834, 816, 565, 354, 506, 31, 912, 155, 290, 667, 830, 189, 120, 815, 854, 757, 71, 47, 45, 947, 317, 901, 122, 818, 128, 329, 934]
def p2 : List Nat := [678, 720, 435, 680, 15, 346, 872, 238, 338, 764, 728, 799, 271, 538, 781, 597, 306, 143, 508, 894, 787, 855, 389, 903, 445, 234, 67, 83, 898, 535, 401, 423, 631, 798, 802, 926, 727, 804, 545, 660, 255, 274, 278, 475, 346, 1003, 848, 487, 741, 1, 686, 668, 635, 964, 301, 99, 616, 348, 898, 458]
def p3 : List Nat := [962, 801, 519, 215, 692, 518, 713, 621, 41, 678, 742, 185, 641, 845, 794, 143, 300, 789, 629, 325, 105, 173, 805, 172, 993, 843, 968, 296, 917, 219, 489, 863, 44, 399, 116, 459, 668, 115, 772, 272, 963, 237, 517, 156, 171, 230, 66, 530, 213, 867, 69, 835, 365, 689, 319, 149, 322, 589, 120]
def p4 : List Nat := [287, 139, 460, 886, 731, 749, 120, 676, 401, 132, 451, 241, 323, 551, 145, 430, 453, 388, 691, 826, 175, 439, 533, 283, 122, 341, 874, 982, 374, 753, 296, 456, 473, 546, 578, 864, 272, 827, 648, 722, 596, 59, 597, 615, 147, 30, 394, 473, 644, 365, 101, 96, 57, 943, 684, 140, 702, 675]
def p5 : List Nat := [773, 420, 18, 999, 746, 667, 13, 417, 727, 324, 287, 598, 701, 78, 979, 545, 669, 366, 811, 589, 503, 211, 219, 668, 625, 588, 54, 387, 203, 145, 951, 60, 142, 552, 498, 589, 542, 309, 452, 144, 417, 889, 774, 183, 818, 107, 802, 213, 646, 213, 613, 960, 924, 596, 46, 831, 461]
def p6 : List Nat := [698, 853, 66, 72, 707, 604, 507, 688, 145, 471, 296, 690, 708, 13, 163, 506, 720, 703, 491, 23, 769, 542, 278, 267, 187, 488, 433, 751, 384, 585, 39, 375, 792, 236, 86, 771, 238, 413, 451, 182, 414, 299, 981, 164, 2, 630, 918, 779, 419, 825, 485, 862, 685, 265, 752, 710]
def p7 : List Nat := [518, 860, 876, 822, 765, 544, 189, 526, 71, 966, 316, 611, 247, 627, 705, 657, 170, 507, 881, 202, 732, 249, 946, 815, 238, 600, 816, 200, 323, 445, 512, 890, 286, 554, 5, 780, 282, 110, 169, 90, 302, 457, 83, 33, 713, 471, 756, 117, 599, 775, 281, 914, 607, 689, 317]
def p8 : List Nat := [878, 922, 742, 546, 943, 126, 459, 493, 43, 893, 889, 737, 113, 604, 475, 433, 1008, 102, 610, 254, 168, 822, 58, 980, 527, 806, 468, 911, 403, 369, 546, 902, 38, 822, 515, 360, 494, 499, 632, 421, 880, 446, 697, 138, 445, 354, 391, 76, 548, 323, 776, 915, 952, 557]
def p9 : List Nat := [804, 307, 806, 701, 533, 700, 954, 870, 270, 958, 167, 236, 478, 1007, 749, 398, 670, 141, 149, 356, 720, 48, 431, 225, 400, 794, 887, 798, 210, 128, 212, 709, 173, 177, 595, 382, 454, 227, 381, 375, 725, 113, 953, 192, 132, 175, 655, 322, 913, 119, 65, 23, 300]
def p10 : List Nat := [756, 302, 920, 720, 406, 461, 636, 1005, 599, 541, 0, 145, 83, 545, 1006, 265, 349, 946, 666, 860, 10, 508, 60, 99, 981, 485, 521, 178, 803, 924, 635, 930, 506, 830, 365, 63, 482, 674, 891, 727, 203, 339, 535, 203, 298, 974, 864, 508, 10, 765, 509, 267]
def p11 : List Nat := [215, 167, 843, 192, 364, 932, 385, 196, 344, 127, 160, 765, 11, 205, 887, 211, 939, 122, 227, 253, 83, 809, 929, 462, 539, 261, 13, 605, 344, 151, 363, 293, 136, 581, 849, 347, 229, 337, 28, 264, 812, 9, 339, 302, 790, 768, 188, 781, 150, 238, 370]
def p12 : List Nat := [735, 20, 806, 396, 265, 449, 799, 72, 4, 799, 373, 88, 577, 855, 151, 208, 884, 81, 760, 910, 750, 652, 996, 458, 11, 787, 309, 526, 341, 410, 843, 726, 844, 495, 501, 2, 672, 164, 368, 25, 878, 448, 783, 744, 337, 25, 391, 327, 220, 55]
def p13 : List Nat := [210, 77, 142, 355, 382, 446, 786, 281, 5, 36, 291, 353, 781, 771, 508, 58, 753, 719, 792, 463, 991, 562, 909, 912, 770, 971, 559, 351, 690, 236, 57, 963, 607, 761, 522, 856, 971, 492, 924, 4, 309, 18, 257, 608, 900, 900, 814, 655, 625]
def p14 : List Nat := [581, 537, 87, 403, 855, 987, 256, 421, 842, 530, 108, 791, 810, 11, 725, 110, 585, 257, 124, 377, 335, 602, 62, 807, 628, 922, 828, 510, 240, 526, 732, 39, 263, 984, 810, 375, 751, 194, 196, 43, 982, 900, 636, 367, 689, 93, 253, 967]
def p15 : List Nat := [119, 200, 24, 792, 471, 581, 888, 542, 350, 1004, 489, 209, 242, 272, 603, 371, 425, 40, 651, 538, 411, 543, 185, 804, 207, 960, 768, 198, 781, 606, 140, 360, 956, 651, 813, 689, 68, 278, 205, 746, 745, 110, 237, 62, 191, 185, 261]
def p16 : List Nat := [602, 455, 339, 563, 953, 537, 863, 197, 787, 844, 289, 706, 930, 817, 487, 31, 221, 108, 787, 546, 782, 985, 137, 175, 96, 435, 942, 777, 248, 322, 318, 181, 23, 797, 434, 1004, 236, 795, 427, 209, 41, 222, 731, 281, 498, 900]
def p17 : List Nat := [813, 190, 516, 91, 907, 129, 708, 1005, 421, 386, 422, 574, 1005, 382, 501, 371, 822, 258, 657, 29, 317, 119, 392, 91, 370, 216, 901, 1005, 283, 925, 778, 113, 979, 335, 531, 348, 576, 131, 252, 980, 146, 757, 113, 295, 746]
def p18 : List Nat := [30, 431, 947, 65, 87, 93, 118, 25, 496, 791, 604, 727, 568, 371, 316, 757, 607, 479, 6, 997, 9, 364, 4, 465, 278, 845, 402, 713, 728, 50, 452, 257, 415, 488, 70, 252, 484, 63, 223, 68, 662, 879, 973, 283]
def p19 : List Nat := [352, 49, 489, 100, 391, 106, 225, 699, 998, 651, 544, 592, 785, 137, 536, 541, 498, 198, 391, 373, 364, 79, 192, 14, 126, 310, 653, 170, 528, 485, 140, 754, 799, 579, 799, 961, 918, 232, 889, 351, 594, 722, 437]
def p20 : List Nat := [638, 464, 223, 806, 706, 496, 612, 280, 560, 931, 608, 544, 728, 899, 761, 362, 777, 577, 423, 577, 189, 864, 126, 436, 873, 649, 71, 767, 260, 902, 237, 288, 196, 414, 500, 104, 42, 992, 949, 375, 738, 342]
def p21 : List Nat := [9, 401, 409, 923, 549, 498, 28, 747, 58, 481, 476, 739, 342, 186, 534, 962, 629, 351, 287, 642, 215, 741, 975, 713, 431, 794, 855, 451, 663, 240, 719, 416, 3, 779, 599, 230, 293, 188, 869, 254, 813]
def p22 : List Nat := [407, 624, 189, 271, 941, 399, 323, 471, 893, 973, 655, 665, 251, 140, 373, 84, 753, 336, 461, 960, 225, 516, 785, 760, 503, 910, 824, 406, 802, 357, 638, 993, 536, 272, 381, 864, 137, 937, 601, 290]
def p23 : List Nat := [642, 640, 936, 872, 375, 849, 846, 230, 440, 419, 490, 266, 461, 680, 81, 923, 439, 795, 364, 108, 396, 266, 699, 878, 736, 264, 439, 124, 729, 660, 123, 563, 665, 30, 346, 414, 951, 884, 424]
def p24 : List Nat := [577, 868, 922, 639, 559, 293, 810, 702, 680, 602, 407, 166, 913, 350, 340, 746, 37, 152, 60, 532, 675, 186, 347, 993, 877, 832, 316, 805, 551, 603, 438, 424, 103, 264, 119, 931, 684, 553]
def p25 : List Nat := [211, 618, 568, 850, 903, 947, 402, 721, 297, 562, 176, 472, 791, 713, 814, 628, 424, 628, 369, 698, 450, 186, 878, 988, 51, 932, 779, 499, 535, 828, 285, 401, 606, 280, 581, 778, 397]
def p26 : List Nat := [479, 820, 398, 442, 426, 229, 967, 642, 425, 154, 442, 526, 647, 20, 698, 857, 21, 791, 586, 979, 483, 339, 840, 381, 321, 342, 14, 441, 979, 683, 687, 869, 695, 582, 695, 527]
def p27 : List Nat := [252, 988, 133, 135, 358, 517, 858, 873, 663, 261, 89, 795, 292, 323, 394, 778, 185, 881, 212, 31, 638, 445, 237, 788, 366, 887, 234, 147, 969, 734, 973, 921, 409, 383, 246]
def p28 : List Nat := [727, 563, 969, 996, 944, 15, 463, 208, 511, 722, 473, 639, 401, 710, 285, 770, 720, 290, 904, 453, 947, 918, 417, 706, 97, 191, 324, 150, 21, 909, 94, 656, 470, 897]
def p29 : List Nat := [514, 979, 25, 416, 426, 169, 293, 799, 503, 921, 886, 536, 872, 120, 18, 220, 998, 909, 682, 96, 993, 44, 919, 401, 276, 339, 152, 500, 467, 797, 642, 851, 212]
def p30 : List Nat := [912, 585, 939, 907, 599, 449, 672, 653, 953, 257, 934, 461, 400, 722, 738, 160, 614, 950, 903, 778, 112, 561, 396, 698, 343, 183, 893, 309, 116, 914, 323, 780]
def p31 : List Nat := [984, 182, 330, 1001, 619, 448, 270, 9, 438, 955, 957, 980, 970, 558, 377, 265, 361, 788, 249, 528, 391, 634, 663, 2, 938, 469, 849, 556, 459, 245, 941]
def p32 : List Nat := [488, 574, 409, 155, 849, 10, 27, 738, 992, 740, 558, 555, 517, 192, 774, 64, 738, 932, 8, 633, 236, 704, 974, 386, 591, 134, 817, 76, 252, 446]
def p33 : List Nat := [900, 261, 754, 319, 79, 180, 221, 997, 552, 884, 457, 24, 913, 87, 77, 432, 228, 780, 322, 501, 311, 313, 347, 831, 914, 396, 822, 230, 545]
def p34 : List Nat := [560, 563, 362, 875, 47, 430, 789, 267, 104, 182, 127, 217, 396, 289, 1000, 147, 8, 382, 851, 905, 998, 389, 696, 3, 842, 737, 809, 340]
def p35 : List Nat := [255, 124, 256, 352, 998, 399, 190, 624, 248, 248, 506, 739, 232, 290, 516, 815, 600, 784, 889, 289, 705, 536, 713, 112, 676, 110, 119]
def p36 : List Nat := [756, 443, 655, 439, 996, 490, 349, 392, 259, 114, 744, 887, 209, 338, 100, 636, 201, 623, 240, 67, 782, 266, 790, 222, 729, 15]
def p37 : List Nat := [607, 187, 302, 672, 186, 379, 672, 138, 495, 117, 137, 569, 175, 361, 544, 526, 504, 481, 216, 573, 229, 794, 554, 979, 638]
def p38 : List Nat := [738, 649, 802, 713, 863, 692, 569, 799, 998, 865, 893, 958, 747, 534, 685, 581, 832, 339, 919, 719, 559, 77, 664, 741]
def p39 : List Nat := [946, 209, 578, 285, 753, 316, 40, 532, 609, 567, 662, 627, 288, 434, 671, 398, 651, 889, 450, 66, 958, 154, 314]
def p40 : List Nat := [57, 445, 602, 173, 970, 309, 861, 352, 188, 695, 332, 224, 228, 424, 520, 675, 66, 455, 881, 645, 513, 672]
def p41 : List Nat := [992, 951, 539, 296, 210, 677, 553, 21, 882, 105, 49, 59, 31, 449, 517, 304, 157, 125, 726, 573, 449]
def p42 : List Nat := [431, 288, 177, 160, 943, 802, 1, 150, 182, 856, 389, 801, 424, 875, 582, 56, 811, 315, 194, 211]
def p43 : List Nat := [277, 63, 691, 647, 167, 383, 57, 447, 686, 784, 937, 441, 853, 121, 956, 893, 892, 544, 260]
def p44 : List Nat := [327, 678, 592, 797, 680, 790, 361, 455, 323, 29, 68, 704, 960, 538, 469, 622, 845, 219]
def p45 : List Nat := [973, 136, 507, 746, 428, 190, 928, 763, 967, 1003, 751, 70, 13, 995, 861, 297, 89]
def p46 : List Nat := [958, 426, 995, 2, 300, 224, 137, 146, 510, 24, 106, 498, 159, 325, 616, 29]
def p47 : List Nat := [533, 642, 212, 197, 593, 433, 625, 864, 535, 615, 443, 42, 847, 359, 202]
def p48 : List Nat := [126, 201, 722, 12, 218, 91, 977, 705, 323, 191, 828, 675, 179, 23]
def p49 : List Nat := [890, 741, 390, 602, 301, 85, 671, 971, 223, 915, 278, 232, 215]
def p50 : List Nat := [705, 650, 489, 434, 897, 20, 823, 652, 19, 531, 281, 106]
def p51 : List Nat := [595, 230, 838, 820, 809, 923, 543, 613, 724, 40, 248]
def p52 : List Nat := [351, 888, 882, 1006, 584, 423, 412, 693, 546, 852]
def p53 : List Nat := [145, 522, 402, 249, 732, 574, 666, 493, 476]
def p54 : List Nat := [627, 396, 104, 533, 669, 820, 166, 809]
def p55 : List Nat := [22, 627, 250, 346, 737, 387, 540]
def p56 : List Nat := [729, 471, 629, 684, 365, 662]
def p57 : List Nat := [263, 169, 764, 325, 402]
def p58 : List Nat := [175, 505, 388, 813]
def p59 : List Nat := [732, 339, 724]
def p60 : List Nat := [937, 201]
def p61 : List Nat := [584]
def p62 : List Nat := []

private theorem tail61 : CheckedEuclid 1009 p61 p62 :=
  CheckedEuclid.done p61 (by decide) (by decide)
private theorem tail60 : CheckedEuclid 1009 p60 p61 :=
  CheckedEuclid.step (q := [456, 745]) (r := p62)
    (by decide_cbv) tail61
private theorem tail59 : CheckedEuclid 1009 p59 p60 :=
  CheckedEuclid.step (q := [54, 104]) (r := p61)
    (by decide_cbv) tail60
private theorem tail58 : CheckedEuclid 1009 p58 p59 :=
  CheckedEuclid.step (q := [520, 730]) (r := p60)
    (by decide_cbv) tail59
private theorem tail57 : CheckedEuclid 1009 p57 p58 :=
  CheckedEuclid.step (q := [522, 626]) (r := p59)
    (by decide_cbv) tail58
private theorem tail56 : CheckedEuclid 1009 p56 p57 :=
  CheckedEuclid.step (q := [75, 343]) (r := p58)
    (by decide_cbv) tail57
private theorem tail55 : CheckedEuclid 1009 p55 p56 :=
  CheckedEuclid.step (q := [545, 580]) (r := p57)
    (by decide_cbv) tail56
private theorem tail54 : CheckedEuclid 1009 p54 p55 :=
  CheckedEuclid.step (q := [454, 37]) (r := p56)
    (by decide_cbv) tail55
private theorem tail53 : CheckedEuclid 1009 p53 p54 :=
  CheckedEuclid.step (q := [314, 825]) (r := p55)
    (by decide_cbv) tail54
private theorem tail52 : CheckedEuclid 1009 p52 p53 :=
  CheckedEuclid.step (q := [687, 926]) (r := p54)
    (by decide_cbv) tail53
private theorem tail51 : CheckedEuclid 1009 p51 p52 :=
  CheckedEuclid.step (q := [260, 474]) (r := p53)
    (by decide_cbv) tail52
private theorem tail50 : CheckedEuclid 1009 p50 p51 :=
  CheckedEuclid.step (q := [160, 806]) (r := p52)
    (by decide_cbv) tail51
private theorem tail49 : CheckedEuclid 1009 p49 p50 :=
  CheckedEuclid.step (q := [394, 240]) (r := p51)
    (by decide_cbv) tail50
private theorem tail48 : CheckedEuclid 1009 p48 p49 :=
  CheckedEuclid.step (q := [556, 812]) (r := p50)
    (by decide_cbv) tail49
private theorem tail47 : CheckedEuclid 1009 p47 p48 :=
  CheckedEuclid.step (q := [838, 272]) (r := p49)
    (by decide_cbv) tail48
private theorem tail46 : CheckedEuclid 1009 p46 p47 :=
  CheckedEuclid.step (q := [100, 145]) (r := p48)
    (by decide_cbv) tail47
private theorem tail45 : CheckedEuclid 1009 p45 p46 :=
  CheckedEuclid.step (q := [209, 351]) (r := p47)
    (by decide_cbv) tail46
private theorem tail44 : CheckedEuclid 1009 p44 p45 :=
  CheckedEuclid.step (q := [494, 626]) (r := p46)
    (by decide_cbv) tail45
private theorem tail43 : CheckedEuclid 1009 p43 p44 :=
  CheckedEuclid.step (q := [507, 766]) (r := p45)
    (by decide_cbv) tail44
private theorem tail42 : CheckedEuclid 1009 p42 p43 :=
  CheckedEuclid.step (q := [259, 548]) (r := p44)
    (by decide_cbv) tail43
private theorem tail41 : CheckedEuclid 1009 p41 p42 :=
  CheckedEuclid.step (q := [4, 992]) (r := p43)
    (by decide_cbv) tail42
private theorem tail40 : CheckedEuclid 1009 p40 p41 :=
  CheckedEuclid.step (q := [22, 806]) (r := p42)
    (by decide_cbv) tail41
private theorem tail39 : CheckedEuclid 1009 p39 p40 :=
  CheckedEuclid.step (q := [70, 538]) (r := p41)
    (by decide_cbv) tail40
private theorem tail38 : CheckedEuclid 1009 p38 p39 :=
  CheckedEuclid.step (q := [806, 12]) (r := p40)
    (by decide_cbv) tail39
private theorem tail37 : CheckedEuclid 1009 p37 p38 :=
  CheckedEuclid.step (q := [906, 472]) (r := p39)
    (by decide_cbv) tail38
private theorem tail36 : CheckedEuclid 1009 p36 p37 :=
  CheckedEuclid.step (q := [768, 669]) (r := p38)
    (by decide_cbv) tail37
private theorem tail35 : CheckedEuclid 1009 p35 p36 :=
  CheckedEuclid.step (q := [133, 277]) (r := p37)
    (by decide_cbv) tail36
private theorem tail34 : CheckedEuclid 1009 p34 p35 :=
  CheckedEuclid.step (q := [846, 147]) (r := p36)
    (by decide_cbv) tail35
private theorem tail33 : CheckedEuclid 1009 p33 p34 :=
  CheckedEuclid.step (q := [857, 699]) (r := p35)
    (by decide_cbv) tail34
private theorem tail32 : CheckedEuclid 1009 p32 p33 :=
  CheckedEuclid.step (q := [121, 447]) (r := p34)
    (by decide_cbv) tail33
private theorem tail31 : CheckedEuclid 1009 p31 p32 :=
  CheckedEuclid.step (q := [637, 303]) (r := p33)
    (by decide_cbv) tail32
private theorem tail30 : CheckedEuclid 1009 p30 p31 :=
  CheckedEuclid.step (q := [427, 404]) (r := p32)
    (by decide_cbv) tail31
private theorem tail29 : CheckedEuclid 1009 p29 p30 :=
  CheckedEuclid.step (q := [785, 378]) (r := p31)
    (by decide_cbv) tail30
private theorem tail28 : CheckedEuclid 1009 p28 p29 :=
  CheckedEuclid.step (q := [724, 266]) (r := p30)
    (by decide_cbv) tail29
private theorem tail27 : CheckedEuclid 1009 p27 p28 :=
  CheckedEuclid.step (q := [738, 196]) (r := p29)
    (by decide_cbv) tail28
private theorem tail26 : CheckedEuclid 1009 p26 p27 :=
  CheckedEuclid.step (q := [992, 400]) (r := p28)
    (by decide_cbv) tail27
private theorem tail25 : CheckedEuclid 1009 p25 p26 :=
  CheckedEuclid.step (q := [516, 780]) (r := p27)
    (by decide_cbv) tail26
private theorem tail24 : CheckedEuclid 1009 p24 p25 :=
  CheckedEuclid.step (q := [230, 436]) (r := p26)
    (by decide_cbv) tail25
private theorem tail23 : CheckedEuclid 1009 p23 p24 :=
  CheckedEuclid.step (q := [333, 300]) (r := p25)
    (by decide_cbv) tail24
private theorem tail22 : CheckedEuclid 1009 p22 p23 :=
  CheckedEuclid.step (q := [861, 34]) (r := p24)
    (by decide_cbv) tail23
private theorem tail21 : CheckedEuclid 1009 p21 p22 :=
  CheckedEuclid.step (q := [348, 222]) (r := p23)
    (by decide_cbv) tail22
private theorem tail20 : CheckedEuclid 1009 p20 p21 :=
  CheckedEuclid.step (q := [362, 894]) (r := p22)
    (by decide_cbv) tail21
private theorem tail19 : CheckedEuclid 1009 p19 p20 :=
  CheckedEuclid.step (q := [970, 730]) (r := p21)
    (by decide_cbv) tail20
private theorem tail18 : CheckedEuclid 1009 p18 p19 :=
  CheckedEuclid.step (q := [90, 661]) (r := p20)
    (by decide_cbv) tail19
private theorem tail17 : CheckedEuclid 1009 p17 p18 :=
  CheckedEuclid.step (q := [49, 377]) (r := p19)
    (by decide_cbv) tail18
private theorem tail16 : CheckedEuclid 1009 p16 p17 :=
  CheckedEuclid.step (q := [203, 104]) (r := p18)
    (by decide_cbv) tail17
private theorem tail15 : CheckedEuclid 1009 p15 p16 :=
  CheckedEuclid.step (q := [857, 192]) (r := p17)
    (by decide_cbv) tail16
private theorem tail14 : CheckedEuclid 1009 p14 p15 :=
  CheckedEuclid.step (q := [534, 197]) (r := p16)
    (by decide_cbv) tail15
private theorem tail13 : CheckedEuclid 1009 p13 p14 :=
  CheckedEuclid.step (q := [997, 874]) (r := p15)
    (by decide_cbv) tail14
private theorem tail12 : CheckedEuclid 1009 p12 p13 :=
  CheckedEuclid.step (q := [68, 775]) (r := p14)
    (by decide_cbv) tail13
private theorem tail11 : CheckedEuclid 1009 p11 p12 :=
  CheckedEuclid.step (q := [858, 924]) (r := p13)
    (by decide_cbv) tail12
private theorem tail10 : CheckedEuclid 1009 p10 p11 :=
  CheckedEuclid.step (q := [873, 947]) (r := p12)
    (by decide_cbv) tail11
private theorem tail9 : CheckedEuclid 1009 p9 p10 :=
  CheckedEuclid.step (q := [560, 636]) (r := p11)
    (by decide_cbv) tail10
private theorem tail8 : CheckedEuclid 1009 p8 p9 :=
  CheckedEuclid.step (q := [88, 429]) (r := p10)
    (by decide_cbv) tail9
private theorem tail7 : CheckedEuclid 1009 p7 p8 :=
  CheckedEuclid.step (q := [395, 573]) (r := p9)
    (by decide_cbv) tail8
private theorem tail6 : CheckedEuclid 1009 p6 p7 :=
  CheckedEuclid.step (q := [323, 346]) (r := p8)
    (by decide_cbv) tail7
private theorem tail5 : CheckedEuclid 1009 p5 p6 :=
  CheckedEuclid.step (q := [103, 670]) (r := p7)
    (by decide_cbv) tail6
private theorem tail4 : CheckedEuclid 1009 p4 p5 :=
  CheckedEuclid.step (q := [844, 402]) (r := p6)
    (by decide_cbv) tail5
private theorem tail3 : CheckedEuclid 1009 p3 p4 :=
  CheckedEuclid.step (q := [862, 628]) (r := p5)
    (by decide_cbv) tail4
private theorem tail2 : CheckedEuclid 1009 p2 p3 :=
  CheckedEuclid.step (q := [786, 996]) (r := p4)
    (by decide_cbv) tail3
private theorem tail1 : CheckedEuclid 1009 p1 p2 :=
  CheckedEuclid.step (q := [485, 262]) (r := p3)
    (by decide_cbv) tail2
private theorem tail0 : CheckedEuclid 1009 p0 p1 :=
  CheckedEuclid.step (q := [240]) (r := p2)
    (by decide_cbv) tail1

theorem euclid : CheckedEuclid 1009 p0 p1 := tail0
theorem degreesPreserved : p0.length = 61 ∧ p1.length = 61 ∧
    p0.getLastD 0 % 1009 = 162 ∧ p1.getLastD 0 % 1009 = 934 := by decide

end Pair1

namespace Pair2

def p0 : List Nat := [1008, 35, 729, 840, 968, 462]
def p1 : List Nat := [1, 961, 540, 627, 914, 293, 707]
def p2 : List Nat := [1008, 35, 729, 840, 968, 462]
def p3 : List Nat := [484, 492, 444, 556, 444]
def p4 : List Nat := [524, 212, 373, 831]
def p5 : List Nat := [405, 796, 14]
def p6 : List Nat := [844, 495]
def p7 : List Nat := [784]
def p8 : List Nat := []

private theorem tail7 : CheckedEuclid 1009 p7 p8 :=
  CheckedEuclid.done p7 (by decide) (by decide)
private theorem tail6 : CheckedEuclid 1009 p6 p7 :=
  CheckedEuclid.step (q := [68, 805]) (r := p8)
    (by decide_cbv) tail7
private theorem tail5 : CheckedEuclid 1009 p5 p6 :=
  CheckedEuclid.step (q := [730, 742]) (r := p7)
    (by decide_cbv) tail6
private theorem tail4 : CheckedEuclid 1009 p4 p5 :=
  CheckedEuclid.step (q := [348, 708]) (r := p6)
    (by decide_cbv) tail5
private theorem tail3 : CheckedEuclid 1009 p3 p4 :=
  CheckedEuclid.step (q := [418, 485]) (r := p5)
    (by decide_cbv) tail4
private theorem tail2 : CheckedEuclid 1009 p2 p3 :=
  CheckedEuclid.step (q := [1, 451]) (r := p4)
    (by decide_cbv) tail3
private theorem tail1 : CheckedEuclid 1009 p1 p2 :=
  CheckedEuclid.step (q := [483, 292]) (r := p3)
    (by decide_cbv) tail2
private theorem tail0 : CheckedEuclid 1009 p0 p1 :=
  CheckedEuclid.step (q := []) (r := p2)
    (by decide_cbv) tail1

theorem euclid : CheckedEuclid 1009 p0 p1 := tail0
theorem degreesPreserved : p0.length = 6 ∧ p1.length = 7 ∧
    p0.getLastD 0 % 1009 = 462 ∧ p1.getLastD 0 % 1009 = 707 := by decide

end Pair2

#print axioms J5_moments
#print axioms J6_moments
#print axioms certifyPrime
#print axioms Pair0.euclid
#print axioms Pair0.degreesPreserved
#print axioms Pair1.euclid
#print axioms Pair1.degreesPreserved
#print axioms Pair2.euclid
#print axioms Pair2.degreesPreserved

end RKResearch.Certified.Graded.OrderTwelveFifteen.RadauPencilArithmetic
