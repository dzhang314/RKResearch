import Lean

namespace RKResearch.Certified.Graded.OrderTwelveFifteen.UniformChartUnitArithmetic

set_option maxRecDepth 20000
set_option maxHeartbeats 0

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

-- Expanded receipt: empty_forward_gap.
namespace Pair0

def p0 : List Nat := [631, 457, 44, 982, 23, 360, 378, 385, 115, 659, 254, 181, 93, 905, 686, 787, 798, 591, 793, 643, 428, 952, 792, 875, 735, 896, 615, 676, 355, 652, 134, 241, 433, 629, 945, 983, 1]
def p1 : List Nat := [522, 412, 675, 181, 688, 214, 785, 545, 277, 231, 60, 480, 893, 397, 527, 370, 226, 728, 758, 227, 418, 940, 836, 234, 548, 701, 118, 845, 867, 309, 524, 43, 69, 814, 203, 862]
def p2 : List Nat := [270, 83, 880, 634, 128, 943, 735, 336, 206, 279, 171, 102, 117, 891, 959, 928, 460, 283, 604, 449, 454, 28, 106, 463, 770, 782, 264, 886, 344, 210, 957, 777, 358, 719, 372]
def p3 : List Nat := [435, 3, 700, 655, 685, 837, 240, 412, 2, 893, 771, 180, 824, 991, 303, 819, 864, 892, 862, 751, 739, 88, 52, 965, 538, 311, 432, 402, 907, 757, 444, 780, 71, 454]
def p4 : List Nat := [515, 65, 654, 81, 267, 416, 463, 470, 783, 295, 469, 174, 293, 61, 676, 977, 51, 560, 843, 832, 561, 11, 455, 964, 687, 777, 258, 588, 247, 304, 388, 658, 781]
def p5 : List Nat := [74, 244, 890, 409, 61, 584, 156, 473, 770, 952, 413, 102, 59, 930, 768, 347, 683, 212, 505, 462, 964, 727, 371, 663, 305, 960, 115, 508, 320, 863, 298, 827]
def p6 : List Nat := [399, 333, 691, 728, 122, 179, 1005, 920, 14, 370, 261, 619, 195, 318, 649, 337, 516, 518, 149, 435, 852, 810, 325, 41, 773, 401, 244, 849, 836, 761, 256]
def p7 : List Nat := [193, 176, 834, 501, 189, 377, 834, 224, 604, 354, 534, 906, 785, 983, 237, 40, 160, 475, 8, 523, 79, 557, 128, 694, 603, 222, 291, 860, 876, 178]
def p8 : List Nat := [73, 238, 62, 908, 835, 258, 325, 57, 162, 897, 829, 851, 993, 485, 800, 302, 4, 934, 663, 736, 406, 774, 743, 797, 393, 767, 869, 924, 605]
def p9 : List Nat := [652, 819, 788, 752, 94, 106, 837, 796, 878, 239, 883, 187, 880, 368, 287, 200, 157, 885, 740, 181, 969, 23, 406, 675, 14, 300, 361, 238]
def p10 : List Nat := [233, 452, 791, 193, 741, 729, 859, 666, 659, 641, 350, 5, 54, 5, 776, 985, 259, 346, 737, 235, 262, 74, 162, 641, 1004, 580, 524]
def p11 : List Nat := [576, 341, 304, 640, 254, 230, 144, 694, 251, 0, 874, 146, 170, 654, 95, 127, 26, 322, 931, 781, 205, 681, 764, 34, 818, 604]
def p12 : List Nat := [29, 195, 412, 549, 154, 756, 408, 486, 618, 29, 587, 157, 652, 898, 125, 8, 283, 492, 583, 923, 362, 499, 524, 790, 317]
def p13 : List Nat := [656, 428, 574, 552, 399, 516, 672, 516, 682, 77, 929, 721, 402, 398, 173, 227, 152, 187, 931, 4, 848, 911, 472, 387]
def p14 : List Nat := [636, 479, 821, 841, 266, 106, 763, 989, 407, 907, 33, 347, 741, 473, 591, 765, 712, 863, 526, 396, 735, 326, 255]
def p15 : List Nat := [135, 809, 629, 2, 376, 344, 715, 453, 483, 369, 241, 925, 835, 979, 923, 621, 724, 851, 956, 844, 189, 55]
def p16 : List Nat := [469, 729, 890, 865, 96, 140, 818, 320, 936, 645, 163, 579, 512, 104, 882, 102, 927, 230, 805, 642, 459]
def p17 : List Nat := [789, 982, 420, 669, 918, 341, 837, 506, 794, 455, 422, 980, 867, 254, 67, 922, 116, 923, 957, 786]
def p18 : List Nat := [569, 715, 15, 511, 964, 404, 703, 383, 608, 277, 628, 525, 827, 848, 309, 205, 158, 368, 12]
def p19 : List Nat := [971, 1002, 431, 663, 465, 764, 121, 472, 415, 615, 832, 608, 182, 872, 491, 342, 529, 842]
def p20 : List Nat := [23, 937, 332, 66, 90, 666, 129, 496, 616, 589, 658, 415, 405, 778, 610, 357, 979]
def p21 : List Nat := [529, 89, 918, 322, 465, 318, 243, 606, 913, 920, 264, 803, 1005, 271, 175, 980]
def p22 : List Nat := [477, 883, 512, 913, 624, 694, 791, 356, 400, 543, 142, 580, 757, 940, 968]
def p23 : List Nat := [664, 529, 892, 892, 651, 282, 744, 997, 682, 768, 514, 889, 796, 81]
def p24 : List Nat := [672, 372, 678, 179, 772, 882, 263, 741, 595, 101, 999, 563, 14]
def p25 : List Nat := [612, 432, 453, 553, 949, 612, 11, 409, 643, 663, 519, 609]
def p26 : List Nat := [201, 93, 59, 628, 712, 308, 125, 639, 826, 930, 153]
def p27 : List Nat := [130, 852, 345, 511, 9, 165, 490, 292, 761, 475]
def p28 : List Nat := [939, 695, 214, 113, 615, 39, 646, 129, 103]
def p29 : List Nat := [713, 831, 273, 92, 198, 739, 299, 648]
def p30 : List Nat := [989, 239, 195, 842, 843, 216, 143]
def p31 : List Nat := [886, 692, 659, 153, 681, 200]
def p32 : List Nat := [608, 568, 418, 994, 883]
def p33 : List Nat := [295, 454, 877, 625]
def p34 : List Nat := [243, 752, 683]
def p35 : List Nat := [590, 779]
def p36 : List Nat := [65]
def p37 : List Nat := []

private theorem tail36 : CheckedEuclid 1009 p36 p37 :=
  CheckedEuclid.done p36 (by decide) (by decide)
private theorem tail35 : CheckedEuclid 1009 p35 p36 :=
  CheckedEuclid.step (q := [630, 695]) (r := p37)
    (by decide_cbv) tail36
private theorem tail34 : CheckedEuclid 1009 p34 p35 :=
  CheckedEuclid.step (q := [185, 949]) (r := p36)
    (by decide_cbv) tail35
private theorem tail33 : CheckedEuclid 1009 p33 p34 :=
  CheckedEuclid.step (q := [850, 744]) (r := p35)
    (by decide_cbv) tail34
private theorem tail32 : CheckedEuclid 1009 p32 p33 :=
  CheckedEuclid.step (q := [634, 426]) (r := p34)
    (by decide_cbv) tail33
private theorem tail31 : CheckedEuclid 1009 p31 p32 :=
  CheckedEuclid.step (q := [693, 591]) (r := p33)
    (by decide_cbv) tail32
private theorem tail30 : CheckedEuclid 1009 p30 p31 :=
  CheckedEuclid.step (q := [243, 369]) (r := p32)
    (by decide_cbv) tail31
private theorem tail29 : CheckedEuclid 1009 p29 p30 :=
  CheckedEuclid.step (q := [160, 442]) (r := p31)
    (by decide_cbv) tail30
private theorem tail28 : CheckedEuclid 1009 p28 p29 :=
  CheckedEuclid.step (q := [866, 64]) (r := p30)
    (by decide_cbv) tail29
private theorem tail27 : CheckedEuclid 1009 p27 p28 :=
  CheckedEuclid.step (q := [484, 34]) (r := p29)
    (by decide_cbv) tail28
private theorem tail26 : CheckedEuclid 1009 p26 p27 :=
  CheckedEuclid.step (q := [786, 867]) (r := p28)
    (by decide_cbv) tail27
private theorem tail25 : CheckedEuclid 1009 p25 p26 :=
  CheckedEuclid.step (q := [911, 736]) (r := p27)
    (by decide_cbv) tail26
private theorem tail24 : CheckedEuclid 1009 p24 p25 :=
  CheckedEuclid.step (q := [530, 116]) (r := p26)
    (by decide_cbv) tail25
private theorem tail23 : CheckedEuclid 1009 p23 p24 :=
  CheckedEuclid.step (q := [931, 222]) (r := p25)
    (by decide_cbv) tail24
private theorem tail22 : CheckedEuclid 1009 p22 p23 :=
  CheckedEuclid.step (q := [527, 286]) (r := p24)
    (by decide_cbv) tail23
private theorem tail21 : CheckedEuclid 1009 p21 p22 :=
  CheckedEuclid.step (q := [647, 739]) (r := p23)
    (by decide_cbv) tail22
private theorem tail20 : CheckedEuclid 1009 p20 p21 :=
  CheckedEuclid.step (q := [661, 175]) (r := p22)
    (by decide_cbv) tail21
private theorem tail19 : CheckedEuclid 1009 p19 p20 :=
  CheckedEuclid.step (q := [765, 241]) (r := p21)
    (by decide_cbv) tail20
private theorem tail18 : CheckedEuclid 1009 p18 p19 :=
  CheckedEuclid.step (q := [676, 731]) (r := p20)
    (by decide_cbv) tail19
private theorem tail17 : CheckedEuclid 1009 p17 p18 :=
  CheckedEuclid.step (q := [5, 570]) (r := p19)
    (by decide_cbv) tail18
private theorem tail16 : CheckedEuclid 1009 p16 p17 :=
  CheckedEuclid.step (q := [826, 559]) (r := p18)
    (by decide_cbv) tail17
private theorem tail15 : CheckedEuclid 1009 p15 p16 :=
  CheckedEuclid.step (q := [999, 908]) (r := p17)
    (by decide_cbv) tail16
private theorem tail14 : CheckedEuclid 1009 p14 p15 :=
  CheckedEuclid.step (q := [502, 555]) (r := p16)
    (by decide_cbv) tail15
private theorem tail13 : CheckedEuclid 1009 p13 p14 :=
  CheckedEuclid.step (q := [50, 49]) (r := p15)
    (by decide_cbv) tail14
private theorem tail12 : CheckedEuclid 1009 p12 p13 :=
  CheckedEuclid.step (q := [662, 66]) (r := p14)
    (by decide_cbv) tail13
private theorem tail11 : CheckedEuclid 1009 p11 p12 :=
  CheckedEuclid.step (q := [206, 769]) (r := p13)
    (by decide_cbv) tail12
private theorem tail10 : CheckedEuclid 1009 p10 p11 :=
  CheckedEuclid.step (q := [652, 923]) (r := p12)
    (by decide_cbv) tail11
private theorem tail9 : CheckedEuclid 1009 p9 p10 :=
  CheckedEuclid.step (q := [494, 659]) (r := p11)
    (by decide_cbv) tail10
private theorem tail8 : CheckedEuclid 1009 p8 p9 :=
  CheckedEuclid.step (q := [854, 524]) (r := p10)
    (by decide_cbv) tail9
private theorem tail7 : CheckedEuclid 1009 p7 p8 :=
  CheckedEuclid.step (q := [49, 564]) (r := p9)
    (by decide_cbv) tail8
private theorem tail6 : CheckedEuclid 1009 p6 p7 :=
  CheckedEuclid.step (q := [284, 693]) (r := p8)
    (by decide_cbv) tail7
private theorem tail5 : CheckedEuclid 1009 p5 p6 :=
  CheckedEuclid.step (q := [991, 86]) (r := p7)
    (by decide_cbv) tail6
private theorem tail4 : CheckedEuclid 1009 p4 p5 :=
  CheckedEuclid.step (q := [247, 600]) (r := p6)
    (by decide_cbv) tail5
private theorem tail3 : CheckedEuclid 1009 p3 p4 :=
  CheckedEuclid.step (q := [659, 414]) (r := p5)
    (by decide_cbv) tail4
private theorem tail2 : CheckedEuclid 1009 p2 p3 :=
  CheckedEuclid.step (q := [185, 632]) (r := p4)
    (by decide_cbv) tail3
private theorem tail1 : CheckedEuclid 1009 p1 p2 :=
  CheckedEuclid.step (q := [886, 854]) (r := p3)
    (by decide_cbv) tail2
private theorem tail0 : CheckedEuclid 1009 p0 p1 :=
  CheckedEuclid.step (q := [799, 151]) (r := p2)
    (by decide_cbv) tail1

theorem euclid : CheckedEuclid 1009 p0 p1 := tail0
theorem degreesPreserved : p0.length = 37 ∧ p1.length = 36 ∧
    p0.getLastD 0 % 1009 = 1 ∧ p1.getLastD 0 % 1009 = 862 := by decide

end Pair0

-- Expanded receipt: empty_reverse_gap.
namespace Pair1

def p0 : List Nat := [631, 457, 44, 982, 23, 360, 378, 385, 115, 659, 254, 181, 93, 905, 686, 787, 798, 591, 793, 643, 428, 952, 792, 875, 735, 896, 615, 676, 355, 652, 134, 241, 433, 629, 945, 983, 1]
def p1 : List Nat := [828, 692, 99, 905, 112, 400, 467, 616, 189, 436, 771, 682, 204, 430, 633, 474, 316, 727, 328, 402, 228, 654, 882, 158, 187, 114, 644, 970, 126, 235, 299, 842, 84, 493, 459, 188]
def p2 : List Nat := [277, 382, 103, 127, 611, 7, 317, 989, 247, 808, 168, 267, 684, 268, 176, 367, 668, 442, 296, 685, 579, 996, 901, 769, 162, 349, 772, 966, 737, 334, 89, 356, 268, 417, 163]
def p3 : List Nat := [167, 458, 32, 930, 221, 889, 849, 446, 284, 70, 459, 835, 280, 620, 925, 822, 760, 68, 756, 631, 592, 447, 74, 612, 1005, 960, 406, 221, 277, 580, 636, 7, 89, 902]
def p4 : List Nat := [127, 468, 685, 17, 789, 985, 807, 889, 885, 707, 26, 650, 557, 617, 5, 4, 21, 95, 613, 9, 984, 594, 105, 41, 774, 757, 948, 44, 434, 427, 724, 188, 116]
def p5 : List Nat := [395, 236, 382, 1000, 40, 546, 396, 203, 563, 646, 193, 199, 277, 316, 62, 128, 634, 694, 507, 66, 437, 594, 304, 635, 228, 325, 35, 552, 328, 889, 132, 937]
def p6 : List Nat := [877, 381, 519, 218, 231, 220, 527, 648, 935, 575, 674, 41, 672, 374, 392, 293, 747, 849, 40, 72, 0, 7, 362, 262, 207, 345, 947, 986, 869, 624, 32]
def p7 : List Nat := [677, 822, 291, 28, 37, 848, 820, 807, 528, 627, 666, 252, 149, 20, 754, 63, 500, 217, 245, 736, 599, 258, 349, 477, 467, 627, 508, 3, 690, 892]
def p8 : List Nat := [38, 362, 854, 801, 250, 701, 942, 278, 189, 920, 170, 485, 998, 130, 475, 30, 122, 47, 742, 597, 735, 142, 826, 141, 341, 199, 609, 294, 101]
def p9 : List Nat := [331, 670, 294, 227, 756, 303, 752, 234, 125, 906, 880, 530, 57, 942, 206, 165, 608, 738, 100, 161, 913, 734, 24, 425, 839, 717, 821, 1007]
def p10 : List Nat := [19, 924, 43, 628, 533, 166, 256, 115, 28, 244, 626, 273, 660, 941, 474, 111, 26, 966, 782, 608, 956, 53, 141, 786, 135, 916, 76]
def p11 : List Nat := [133, 149, 773, 136, 210, 791, 319, 901, 978, 382, 1001, 463, 860, 659, 1000, 667, 101, 284, 473, 112, 313, 791, 813, 177, 37, 70]
def p12 : List Nat := [125, 692, 690, 17, 929, 356, 885, 816, 160, 441, 654, 546, 735, 927, 862, 50, 977, 101, 444, 296, 175, 160, 443, 976, 778]
def p13 : List Nat := [449, 508, 347, 85, 315, 804, 574, 59, 995, 268, 949, 725, 561, 728, 163, 969, 523, 819, 324, 137, 362, 308, 922, 469]
def p14 : List Nat := [878, 978, 311, 898, 392, 596, 938, 772, 773, 869, 182, 807, 562, 1003, 734, 581, 631, 986, 76, 393, 201, 202, 1005]
def p15 : List Nat := [651, 410, 209, 110, 92, 519, 335, 759, 365, 803, 536, 74, 715, 704, 234, 851, 464, 541, 254, 370, 605, 713]
def p16 : List Nat := [902, 514, 470, 938, 881, 611, 798, 628, 70, 709, 32, 688, 778, 812, 618, 288, 253, 920, 948, 458, 302]
def p17 : List Nat := [359, 84, 325, 104, 809, 285, 107, 464, 459, 494, 919, 225, 217, 228, 74, 741, 298, 276, 374, 807]
def p18 : List Nat := [983, 537, 640, 736, 930, 445, 79, 42, 843, 393, 860, 160, 395, 66, 767, 199, 505, 982, 814]
def p19 : List Nat := [56, 2, 40, 1007, 241, 588, 502, 675, 530, 871, 646, 138, 321, 381, 616, 809, 619, 693]
def p20 : List Nat := [110, 396, 943, 524, 877, 661, 127, 451, 40, 124, 621, 393, 532, 374, 326, 271, 17]
def p21 : List Nat := [663, 279, 959, 835, 65, 686, 439, 58, 80, 311, 566, 127, 433, 202, 396, 610]
def p22 : List Nat := [605, 449, 483, 801, 317, 210, 461, 772, 228, 106, 456, 584, 377, 836, 663]
def p23 : List Nat := [26, 201, 90, 582, 292, 921, 286, 788, 527, 805, 727, 233, 544, 235]
def p24 : List Nat := [69, 227, 353, 145, 330, 12, 176, 966, 891, 705, 187, 131, 419]
def p25 : List Nat := [244, 115, 842, 586, 209, 987, 511, 866, 418, 90, 531, 461]
def p26 : List Nat := [728, 140, 879, 73, 344, 48, 398, 726, 755, 469, 953]
def p27 : List Nat := [456, 250, 299, 0, 942, 196, 512, 121, 857, 234]
def p28 : List Nat := [859, 900, 811, 593, 681, 246, 966, 888, 59]
def p29 : List Nat := [136, 593, 863, 892, 833, 999, 1002, 144]
def p30 : List Nat := [4, 271, 338, 658, 474, 165, 137]
def p31 : List Nat := [889, 523, 798, 788, 996, 237]
def p32 : List Nat := [930, 434, 220, 703, 36]
def p33 : List Nat := [54, 233, 396, 797]
def p34 : List Nat := [376, 228, 620]
def p35 : List Nat := [239, 718]
def p36 : List Nat := [351]
def p37 : List Nat := []

private theorem tail36 : CheckedEuclid 1009 p36 p37 :=
  CheckedEuclid.done p36 (by decide) (by decide)
private theorem tail35 : CheckedEuclid 1009 p35 p36 :=
  CheckedEuclid.step (q := [452, 370]) (r := p37)
    (by decide_cbv) tail36
private theorem tail34 : CheckedEuclid 1009 p34 p35 :=
  CheckedEuclid.step (q := [950, 993]) (r := p36)
    (by decide_cbv) tail35
private theorem tail33 : CheckedEuclid 1009 p33 p34 :=
  CheckedEuclid.step (q := [131, 566]) (r := p35)
    (by decide_cbv) tail34
private theorem tail32 : CheckedEuclid 1009 p32 p33 :=
  CheckedEuclid.step (q := [85, 590]) (r := p34)
    (by decide_cbv) tail33
private theorem tail31 : CheckedEuclid 1009 p31 p32 :=
  CheckedEuclid.step (q := [462, 427]) (r := p33)
    (by decide_cbv) tail32
private theorem tail30 : CheckedEuclid 1009 p30 p31 :=
  CheckedEuclid.step (q := [899, 388]) (r := p32)
    (by decide_cbv) tail31
private theorem tail29 : CheckedEuclid 1009 p29 p30 :=
  CheckedEuclid.step (q := [64, 222]) (r := p31)
    (by decide_cbv) tail30
private theorem tail28 : CheckedEuclid 1009 p28 p29 :=
  CheckedEuclid.step (q := [904, 596]) (r := p30)
    (by decide_cbv) tail29
private theorem tail27 : CheckedEuclid 1009 p27 p28 :=
  CheckedEuclid.step (q := [536, 346]) (r := p29)
    (by decide_cbv) tail28
private theorem tail26 : CheckedEuclid 1009 p26 p27 :=
  CheckedEuclid.step (q := [502, 86]) (r := p28)
    (by decide_cbv) tail27
private theorem tail25 : CheckedEuclid 1009 p25 p26 :=
  CheckedEuclid.step (q := [604, 226]) (r := p27)
    (by decide_cbv) tail26
private theorem tail24 : CheckedEuclid 1009 p24 p25 :=
  CheckedEuclid.step (q := [936, 837]) (r := p26)
    (by decide_cbv) tail25
private theorem tail23 : CheckedEuclid 1009 p23 p24 :=
  CheckedEuclid.step (q := [728, 487]) (r := p25)
    (by decide_cbv) tail24
private theorem tail22 : CheckedEuclid 1009 p22 p23 :=
  CheckedEuclid.step (q := [952, 488]) (r := p24)
    (by decide_cbv) tail23
private theorem tail21 : CheckedEuclid 1009 p21 p22 :=
  CheckedEuclid.step (q := [930, 424]) (r := p23)
    (by decide_cbv) tail22
private theorem tail20 : CheckedEuclid 1009 p20 p21 :=
  CheckedEuclid.step (q := [86, 574]) (r := p22)
    (by decide_cbv) tail21
private theorem tail19 : CheckedEuclid 1009 p19 p20 :=
  CheckedEuclid.step (q := [22, 753]) (r := p21)
    (by decide_cbv) tail20
private theorem tail18 : CheckedEuclid 1009 p18 p19 :=
  CheckedEuclid.step (q := [430, 834]) (r := p20)
    (by decide_cbv) tail19
private theorem tail17 : CheckedEuclid 1009 p17 p18 :=
  CheckedEuclid.step (q := [260, 89]) (r := p19)
    (by decide_cbv) tail18
private theorem tail16 : CheckedEuclid 1009 p16 p17 :=
  CheckedEuclid.step (q := [219, 508]) (r := p18)
    (by decide_cbv) tail17
private theorem tail15 : CheckedEuclid 1009 p15 p16 :=
  CheckedEuclid.step (q := [101, 567]) (r := p17)
    (by decide_cbv) tail16
private theorem tail14 : CheckedEuclid 1009 p14 p15 :=
  CheckedEuclid.step (q := [265, 150]) (r := p16)
    (by decide_cbv) tail15
private theorem tail13 : CheckedEuclid 1009 p13 p14 :=
  CheckedEuclid.step (q := [533, 135]) (r := p15)
    (by decide_cbv) tail14
private theorem tail12 : CheckedEuclid 1009 p12 p13 :=
  CheckedEuclid.step (q := [259, 376]) (r := p14)
    (by decide_cbv) tail13
private theorem tail11 : CheckedEuclid 1009 p11 p12 :=
  CheckedEuclid.step (q := [393, 122]) (r := p13)
    (by decide_cbv) tail12
private theorem tail10 : CheckedEuclid 1009 p10 p11 :=
  CheckedEuclid.step (q := [113, 520]) (r := p12)
    (by decide_cbv) tail11
private theorem tail9 : CheckedEuclid 1009 p9 p10 :=
  CheckedEuclid.step (q := [807, 770]) (r := p11)
    (by decide_cbv) tail10
private theorem tail8 : CheckedEuclid 1009 p8 p9 :=
  CheckedEuclid.step (q := [564, 454]) (r := p10)
    (by decide_cbv) tail9
private theorem tail7 : CheckedEuclid 1009 p7 p8 :=
  CheckedEuclid.step (q := [965, 848]) (r := p9)
    (by decide_cbv) tail8
private theorem tail6 : CheckedEuclid 1009 p6 p7 :=
  CheckedEuclid.step (q := [116, 819]) (r := p8)
    (by decide_cbv) tail7
private theorem tail5 : CheckedEuclid 1009 p5 p6 :=
  CheckedEuclid.step (q := [48, 250]) (r := p7)
    (by decide_cbv) tail6
private theorem tail4 : CheckedEuclid 1009 p4 p5 :=
  CheckedEuclid.step (q := [228, 615]) (r := p6)
    (by decide_cbv) tail5
private theorem tail3 : CheckedEuclid 1009 p3 p4 :=
  CheckedEuclid.step (q := [316, 895]) (r := p5)
    (by decide_cbv) tail4
private theorem tail2 : CheckedEuclid 1009 p2 p3 :=
  CheckedEuclid.step (q := [448, 668]) (r := p4)
    (by decide_cbv) tail3
private theorem tail1 : CheckedEuclid 1009 p1 p2 :=
  CheckedEuclid.step (q := [414, 224]) (r := p3)
    (by decide_cbv) tail2
private theorem tail0 : CheckedEuclid 1009 p0 p1 :=
  CheckedEuclid.step (q := [929, 424]) (r := p2)
    (by decide_cbv) tail1

theorem euclid : CheckedEuclid 1009 p0 p1 := tail0
theorem degreesPreserved : p0.length = 37 ∧ p1.length = 36 ∧
    p0.getLastD 0 % 1009 = 1 ∧ p1.getLastD 0 % 1009 = 188 := by decide

end Pair1

-- Expanded receipt: forward_first_diagonal.
namespace Pair2

def p0 : List Nat := [631, 457, 44, 982, 23, 360, 378, 385, 115, 659, 254, 181, 93, 905, 686, 787, 798, 591, 793, 643, 428, 952, 792, 875, 735, 896, 615, 676, 355, 652, 134, 241, 433, 629, 945, 983, 1]
def p1 : List Nat := [799, 207, 126, 21, 91, 374, 882, 697, 537, 216, 814, 559, 776, 631, 649, 873, 643, 1003, 417, 908, 0, 115, 334, 182, 152, 681, 448, 638, 618, 991, 535, 845, 918, 467, 790, 698]
def p2 : List Nat := [310, 369, 794, 340, 302, 207, 28, 47, 342, 718, 285, 140, 184, 817, 731, 170, 822, 594, 540, 9, 817, 335, 190, 678, 354, 158, 633, 840, 553, 965, 558, 292, 465, 727, 137]
def p3 : List Nat := [977, 390, 189, 109, 726, 341, 329, 536, 608, 206, 978, 179, 469, 114, 337, 541, 314, 808, 19, 563, 544, 168, 19, 234, 268, 586, 158, 229, 61, 791, 511, 298, 95, 86]
def p4 : List Nat := [80, 727, 902, 158, 586, 532, 839, 278, 925, 224, 108, 662, 36, 593, 694, 323, 947, 211, 394, 419, 721, 101, 78, 426, 130, 80, 533, 819, 150, 571, 919, 209, 41]
def p5 : List Nat := [563, 29, 17, 275, 880, 220, 99, 853, 969, 547, 690, 554, 68, 759, 228, 434, 89, 51, 578, 618, 747, 79, 901, 867, 369, 613, 246, 851, 600, 458, 302, 640]
def p6 : List Nat := [571, 688, 289, 519, 241, 648, 625, 325, 89, 697, 389, 171, 996, 641, 467, 688, 440, 166, 525, 194, 876, 321, 724, 602, 581, 290, 277, 236, 865, 325, 469]
def p7 : List Nat := [856, 825, 539, 95, 791, 538, 571, 235, 290, 767, 543, 626, 618, 871, 995, 23, 328, 593, 411, 619, 802, 699, 298, 727, 519, 717, 913, 810, 395, 685]
def p8 : List Nat := [990, 306, 610, 752, 772, 26, 453, 207, 354, 118, 433, 150, 575, 899, 155, 833, 31, 475, 73, 122, 431, 196, 141, 383, 243, 805, 987, 908, 537]
def p9 : List Nat := [280, 792, 854, 832, 612, 6, 108, 541, 323, 437, 100, 945, 664, 70, 161, 910, 349, 136, 852, 573, 67, 404, 564, 40, 761, 179, 522, 720]
def p10 : List Nat := [89, 148, 46, 60, 868, 516, 710, 818, 388, 194, 103, 524, 629, 868, 476, 942, 389, 508, 305, 349, 352, 849, 838, 403, 7, 444, 814]
def p11 : List Nat := [919, 269, 604, 837, 177, 955, 981, 95, 280, 532, 457, 905, 978, 106, 392, 615, 1003, 663, 926, 175, 937, 384, 835, 864, 508, 677]
def p12 : List Nat := [8, 477, 183, 44, 653, 764, 71, 148, 879, 963, 541, 210, 58, 981, 352, 469, 412, 532, 98, 303, 292, 578, 203, 10, 195]
def p13 : List Nat := [237, 598, 279, 378, 838, 94, 287, 571, 249, 28, 578, 65, 233, 967, 834, 856, 198, 661, 755, 705, 186, 331, 462, 220]
def p14 : List Nat := [193, 830, 460, 52, 927, 435, 424, 997, 942, 706, 11, 561, 623, 634, 725, 743, 155, 385, 757, 77, 702, 645, 400]
def p15 : List Nat := [143, 263, 746, 497, 704, 713, 151, 283, 925, 346, 509, 956, 62, 274, 231, 941, 514, 400, 351, 758, 272, 267]
def p16 : List Nat := [719, 428, 643, 638, 97, 790, 62, 750, 410, 979, 295, 706, 383, 38, 827, 619, 348, 948, 221, 833, 579]
def p17 : List Nat := [503, 966, 756, 177, 408, 605, 762, 493, 516, 565, 676, 815, 842, 43, 264, 51, 403, 769, 770, 304]
def p18 : List Nat := [301, 497, 725, 661, 33, 59, 927, 265, 380, 893, 469, 60, 149, 816, 447, 866, 549, 774, 954]
def p19 : List Nat := [497, 432, 964, 733, 442, 687, 871, 947, 678, 934, 543, 864, 588, 371, 981, 81, 197, 478]
def p20 : List Nat := [207, 1000, 578, 425, 749, 769, 117, 843, 188, 145, 135, 974, 886, 938, 66, 66, 620]
def p21 : List Nat := [611, 511, 709, 397, 745, 393, 236, 32, 206, 669, 986, 422, 814, 900, 524, 778]
def p22 : List Nat := [961, 487, 152, 35, 933, 435, 594, 657, 265, 451, 688, 485, 427, 867, 583]
def p23 : List Nat := [188, 568, 747, 210, 408, 785, 291, 516, 811, 271, 317, 565, 206, 101]
def p24 : List Nat := [609, 510, 440, 356, 516, 363, 87, 213, 335, 52, 237, 900, 4]
def p25 : List Nat := [376, 641, 477, 516, 540, 995, 125, 782, 623, 778, 618, 464]
def p26 : List Nat := [423, 845, 9, 873, 924, 205, 661, 550, 611, 239, 83]
def p27 : List Nat := [186, 89, 806, 12, 494, 347, 908, 90, 105, 425]
def p28 : List Nat := [142, 164, 439, 698, 694, 535, 586, 344, 484]
def p29 : List Nat := [277, 485, 160, 544, 262, 243, 441, 841]
def p30 : List Nat := [783, 647, 467, 477, 653, 529, 344]
def p31 : List Nat := [128, 853, 481, 879, 476, 293]
def p32 : List Nat := [226, 567, 492, 267, 419]
def p33 : List Nat := [691, 974, 47, 434]
def p34 : List Nat := [803, 784, 975]
def p35 : List Nat := [466, 578]
def p36 : List Nat := [431]
def p37 : List Nat := []

private theorem tail36 : CheckedEuclid 1009 p36 p37 :=
  CheckedEuclid.done p36 (by decide) (by decide)
private theorem tail35 : CheckedEuclid 1009 p35 p36 :=
  CheckedEuclid.step (q := [481, 1008]) (r := p37)
    (by decide_cbv) tail36
private theorem tail34 : CheckedEuclid 1009 p34 p35 :=
  CheckedEuclid.step (q := [200, 178]) (r := p36)
    (by decide_cbv) tail35
private theorem tail33 : CheckedEuclid 1009 p33 p34 :=
  CheckedEuclid.step (q := [523, 284]) (r := p35)
    (by decide_cbv) tail34
private theorem tail32 : CheckedEuclid 1009 p32 p33 :=
  CheckedEuclid.step (q := [684, 817]) (r := p34)
    (by decide_cbv) tail33
private theorem tail31 : CheckedEuclid 1009 p31 p32 :=
  CheckedEuclid.step (q := [377, 268]) (r := p33)
    (by decide_cbv) tail32
private theorem tail30 : CheckedEuclid 1009 p30 p31 :=
  CheckedEuclid.step (q := [28, 287]) (r := p32)
    (by decide_cbv) tail31
private theorem tail29 : CheckedEuclid 1009 p29 p30 :=
  CheckedEuclid.step (q := [736, 680]) (r := p31)
    (by decide_cbv) tail30
private theorem tail28 : CheckedEuclid 1009 p28 p29 :=
  CheckedEuclid.step (q := [606, 886]) (r := p30)
    (by decide_cbv) tail29
private theorem tail27 : CheckedEuclid 1009 p27 p28 :=
  CheckedEuclid.step (q := [177, 816]) (r := p29)
    (by decide_cbv) tail28
private theorem tail26 : CheckedEuclid 1009 p26 p27 :=
  CheckedEuclid.step (q := [723, 862]) (r := p28)
    (by decide_cbv) tail27
private theorem tail25 : CheckedEuclid 1009 p25 p26 :=
  CheckedEuclid.step (q := [41, 115]) (r := p27)
    (by decide_cbv) tail26
private theorem tail24 : CheckedEuclid 1009 p24 p25 :=
  CheckedEuclid.step (q := [81, 548]) (r := p26)
    (by decide_cbv) tail25
private theorem tail23 : CheckedEuclid 1009 p23 p24 :=
  CheckedEuclid.step (q := [172, 782]) (r := p25)
    (by decide_cbv) tail24
private theorem tail22 : CheckedEuclid 1009 p22 p23 :=
  CheckedEuclid.step (q := [925, 785]) (r := p24)
    (by decide_cbv) tail23
private theorem tail21 : CheckedEuclid 1009 p21 p22 :=
  CheckedEuclid.step (q := [811, 704]) (r := p23)
    (by decide_cbv) tail22
private theorem tail20 : CheckedEuclid 1009 p20 p21 :=
  CheckedEuclid.step (q := [514, 504]) (r := p22)
    (by decide_cbv) tail21
private theorem tail19 : CheckedEuclid 1009 p19 p20 :=
  CheckedEuclid.step (q := [599, 323]) (r := p21)
    (by decide_cbv) tail20
private theorem tail18 : CheckedEuclid 1009 p18 p19 :=
  CheckedEuclid.step (q := [122, 973]) (r := p20)
    (by decide_cbv) tail19
private theorem tail17 : CheckedEuclid 1009 p17 p18 :=
  CheckedEuclid.step (q := [590, 288]) (r := p19)
    (by decide_cbv) tail18
private theorem tail16 : CheckedEuclid 1009 p16 p17 :=
  CheckedEuclid.step (q := [394, 523]) (r := p18)
    (by decide_cbv) tail17
private theorem tail15 : CheckedEuclid 1009 p15 p16 :=
  CheckedEuclid.step (q := [210, 288]) (r := p17)
    (by decide_cbv) tail16
private theorem tail14 : CheckedEuclid 1009 p14 p15 :=
  CheckedEuclid.step (q := [208, 848]) (r := p16)
    (by decide_cbv) tail15
private theorem tail13 : CheckedEuclid 1009 p13 p14 :=
  CheckedEuclid.step (q := [769, 51]) (r := p15)
    (by decide_cbv) tail14
private theorem tail12 : CheckedEuclid 1009 p12 p13 :=
  CheckedEuclid.step (q := [161, 299]) (r := p14)
    (by decide_cbv) tail13
private theorem tail11 : CheckedEuclid 1009 p11 p12 :=
  CheckedEuclid.step (q := [842, 583]) (r := p13)
    (by decide_cbv) tail12
private theorem tail10 : CheckedEuclid 1009 p10 p11 :=
  CheckedEuclid.step (q := [100, 964]) (r := p12)
    (by decide_cbv) tail11
private theorem tail9 : CheckedEuclid 1009 p9 p10 :=
  CheckedEuclid.step (q := [537, 462]) (r := p11)
    (by decide_cbv) tail10
private theorem tail8 : CheckedEuclid 1009 p8 p9 :=
  CheckedEuclid.step (q := [187, 459]) (r := p10)
    (by decide_cbv) tail9
private theorem tail7 : CheckedEuclid 1009 p7 p8 :=
  CheckedEuclid.step (q := [129, 642]) (r := p9)
    (by decide_cbv) tail8
private theorem tail6 : CheckedEuclid 1009 p6 p7 :=
  CheckedEuclid.step (q := [682, 338]) (r := p8)
    (by decide_cbv) tail7
private theorem tail5 : CheckedEuclid 1009 p5 p6 :=
  CheckedEuclid.step (q := [777, 522]) (r := p7)
    (by decide_cbv) tail6
private theorem tail4 : CheckedEuclid 1009 p4 p5 :=
  CheckedEuclid.step (q := [854, 112]) (r := p6)
    (by decide_cbv) tail5
private theorem tail3 : CheckedEuclid 1009 p3 p4 :=
  CheckedEuclid.step (q := [434, 765]) (r := p5)
    (by decide_cbv) tail4
private theorem tail2 : CheckedEuclid 1009 p2 p3 :=
  CheckedEuclid.step (q := [182, 905]) (r := p4)
    (by decide_cbv) tail3
private theorem tail1 : CheckedEuclid 1009 p1 p2 :=
  CheckedEuclid.step (q := [722, 992]) (r := p3)
    (by decide_cbv) tail2
private theorem tail0 : CheckedEuclid 1009 p0 p1 :=
  CheckedEuclid.step (q := [330, 863]) (r := p2)
    (by decide_cbv) tail1

theorem euclid : CheckedEuclid 1009 p0 p1 := tail0
theorem degreesPreserved : p0.length = 37 ∧ p1.length = 36 ∧
    p0.getLastD 0 % 1009 = 1 ∧ p1.getLastD 0 % 1009 = 698 := by decide

end Pair2

-- Expanded receipt: forward_five_dirty.
namespace Pair3

def p0 : List Nat := [631, 457, 44, 982, 23, 360, 378, 385, 115, 659, 254, 181, 93, 905, 686, 787, 798, 591, 793, 643, 428, 952, 792, 875, 735, 896, 615, 676, 355, 652, 134, 241, 433, 629, 945, 983, 1]
def p1 : List Nat := [833, 636, 900, 100, 343, 693, 915, 640, 370, 267, 912, 201, 201, 824, 673, 1003, 606, 735, 586, 940, 430, 263, 368, 963, 235, 730, 347, 309, 364, 625, 963, 373, 477, 274, 395, 325]
def p2 : List Nat := [703, 41, 660, 141, 655, 819, 858, 730, 155, 229, 873, 360, 417, 11, 594, 517, 501, 708, 146, 8, 880, 189, 867, 786, 767, 869, 988, 591, 808, 852, 38, 400, 492, 934, 411]
def p3 : List Nat := [236, 477, 10, 28, 218, 394, 558, 971, 101, 552, 252, 463, 747, 562, 505, 624, 858, 248, 312, 321, 1002, 990, 890, 600, 664, 229, 448, 550, 804, 40, 763, 879, 124, 497]
def p4 : List Nat := [504, 172, 983, 768, 109, 515, 658, 542, 8, 633, 151, 622, 445, 111, 305, 114, 202, 686, 606, 779, 844, 768, 45, 945, 782, 663, 877, 70, 496, 974, 599, 664, 925]
def p5 : List Nat := [336, 338, 510, 483, 115, 32, 64, 223, 867, 797, 788, 643, 15, 250, 954, 229, 988, 290, 383, 970, 185, 34, 470, 297, 953, 567, 753, 904, 732, 221, 911, 691]
def p6 : List Nat := [646, 763, 207, 64, 223, 160, 857, 830, 358, 420, 516, 11, 872, 542, 481, 181, 254, 478, 125, 729, 594, 799, 93, 500, 572, 896, 697, 662, 606, 148, 101]
def p7 : List Nat := [308, 742, 271, 135, 707, 13, 572, 541, 998, 517, 812, 951, 192, 139, 184, 910, 393, 202, 748, 630, 44, 390, 877, 925, 966, 30, 693, 378, 39, 670]
def p8 : List Nat := [737, 448, 918, 450, 672, 696, 131, 571, 539, 30, 421, 937, 406, 815, 583, 310, 989, 643, 177, 535, 0, 471, 447, 750, 336, 870, 20, 638, 900]
def p9 : List Nat := [708, 469, 314, 701, 96, 159, 340, 653, 203, 282, 863, 909, 432, 891, 517, 886, 739, 155, 776, 580, 935, 647, 971, 892, 606, 285, 926, 25]
def p10 : List Nat := [442, 410, 888, 37, 621, 453, 992, 251, 742, 172, 588, 517, 799, 279, 1000, 668, 989, 797, 664, 273, 508, 427, 546, 401, 764, 881, 305]
def p11 : List Nat := [363, 367, 947, 585, 830, 107, 827, 186, 716, 331, 58, 202, 997, 425, 109, 200, 71, 706, 553, 348, 398, 32, 35, 661, 984, 413]
def p12 : List Nat := [574, 561, 560, 624, 121, 201, 885, 935, 63, 447, 734, 264, 673, 577, 316, 676, 275, 526, 222, 72, 712, 634, 910, 544, 237]
def p13 : List Nat := [393, 468, 465, 35, 383, 63, 395, 448, 425, 792, 248, 790, 306, 418, 696, 171, 206, 655, 861, 194, 404, 135, 413, 626]
def p14 : List Nat := [477, 988, 668, 100, 115, 253, 419, 132, 299, 604, 623, 975, 255, 114, 765, 941, 826, 685, 888, 679, 820, 156, 555]
def p15 : List Nat := [224, 148, 362, 65, 158, 450, 221, 363, 108, 598, 489, 613, 104, 114, 899, 225, 790, 91, 821, 595, 235, 223]
def p16 : List Nat := [868, 161, 836, 810, 486, 100, 695, 456, 333, 686, 984, 405, 687, 950, 339, 577, 292, 300, 767, 643, 662]
def p17 : List Nat := [144, 724, 200, 605, 989, 744, 501, 829, 454, 638, 97, 671, 546, 15, 728, 889, 57, 497, 262, 581]
def p18 : List Nat := [879, 27, 861, 524, 543, 841, 234, 583, 289, 185, 867, 116, 57, 36, 400, 721, 8, 315, 462]
def p19 : List Nat := [932, 435, 1006, 624, 131, 225, 1000, 526, 683, 161, 794, 209, 549, 986, 262, 514, 763, 946]
def p20 : List Nat := [793, 136, 182, 72, 181, 712, 367, 161, 432, 940, 899, 22, 626, 970, 109, 600, 991]
def p21 : List Nat := [832, 955, 689, 693, 841, 463, 453, 624, 824, 579, 69, 81, 276, 851, 150, 130]
def p22 : List Nat := [468, 884, 284, 253, 752, 626, 723, 923, 474, 687, 707, 526, 868, 368, 713]
def p23 : List Nat := [57, 539, 892, 467, 585, 70, 844, 769, 546, 558, 172, 225, 82, 789]
def p24 : List Nat := [897, 15, 282, 876, 30, 583, 87, 507, 822, 202, 123, 895, 690]
def p25 : List Nat := [217, 227, 613, 45, 107, 638, 258, 273, 41, 801, 21, 308]
def p26 : List Nat := [876, 112, 903, 508, 365, 975, 581, 141, 995, 382, 696]
def p27 : List Nat := [69, 376, 320, 694, 470, 23, 886, 464, 777, 807]
def p28 : List Nat := [782, 733, 742, 645, 995, 282, 595, 367, 81]
def p29 : List Nat := [908, 418, 676, 338, 564, 522, 745, 546]
def p30 : List Nat := [641, 811, 967, 156, 228, 868, 654]
def p31 : List Nat := [429, 84, 659, 508, 302, 523]
def p32 : List Nat := [167, 258, 919, 731, 964]
def p33 : List Nat := [871, 974, 143, 569]
def p34 : List Nat := [327, 658, 67]
def p35 : List Nat := [462, 308]
def p36 : List Nat := [752]
def p37 : List Nat := []

private theorem tail36 : CheckedEuclid 1009 p36 p37 :=
  CheckedEuclid.done p36 (by decide) (by decide)
private theorem tail35 : CheckedEuclid 1009 p35 p36 :=
  CheckedEuclid.step (q := [540, 360]) (r := p37)
    (by decide_cbv) tail36
private theorem tail34 : CheckedEuclid 1009 p34 p35 :=
  CheckedEuclid.step (q := [10, 698]) (r := p36)
    (by decide_cbv) tail35
private theorem tail33 : CheckedEuclid 1009 p33 p34 :=
  CheckedEuclid.step (q := [785, 641]) (r := p35)
    (by decide_cbv) tail34
private theorem tail32 : CheckedEuclid 1009 p32 p33 :=
  CheckedEuclid.step (q := [279, 539]) (r := p34)
    (by decide_cbv) tail33
private theorem tail31 : CheckedEuclid 1009 p31 p32 :=
  CheckedEuclid.step (q := [523, 818]) (r := p33)
    (by decide_cbv) tail32
private theorem tail30 : CheckedEuclid 1009 p30 p31 :=
  CheckedEuclid.step (q := [114, 908]) (r := p32)
    (by decide_cbv) tail31
private theorem tail29 : CheckedEuclid 1009 p29 p30 :=
  CheckedEuclid.step (q := [654, 223]) (r := p31)
    (by decide_cbv) tail30
private theorem tail28 : CheckedEuclid 1009 p28 p29 :=
  CheckedEuclid.step (q := [608, 549]) (r := p30)
    (by decide_cbv) tail29
private theorem tail27 : CheckedEuclid 1009 p27 p28 :=
  CheckedEuclid.step (q := [746, 720]) (r := p29)
    (by decide_cbv) tail28
private theorem tail26 : CheckedEuclid 1009 p26 p27 :=
  CheckedEuclid.step (q := [908, 556]) (r := p28)
    (by decide_cbv) tail27
private theorem tail25 : CheckedEuclid 1009 p25 p26 :=
  CheckedEuclid.step (q := [272, 215]) (r := p27)
    (by decide_cbv) tail26
private theorem tail24 : CheckedEuclid 1009 p24 p25 :=
  CheckedEuclid.step (q := [944, 35]) (r := p26)
    (by decide_cbv) tail25
private theorem tail23 : CheckedEuclid 1009 p23 p24 :=
  CheckedEuclid.step (q := [578, 453]) (r := p25)
    (by decide_cbv) tail24
private theorem tail22 : CheckedEuclid 1009 p22 p23 :=
  CheckedEuclid.step (q := [258, 992]) (r := p24)
    (by decide_cbv) tail23
private theorem tail21 : CheckedEuclid 1009 p21 p22 :=
  CheckedEuclid.step (q := [504, 170]) (r := p23)
    (by decide_cbv) tail22
private theorem tail20 : CheckedEuclid 1009 p20 p21 :=
  CheckedEuclid.step (q := [363, 93]) (r := p22)
    (by decide_cbv) tail21
private theorem tail19 : CheckedEuclid 1009 p19 p20 :=
  CheckedEuclid.step (q := [803, 508]) (r := p21)
    (by decide_cbv) tail20
private theorem tail18 : CheckedEuclid 1009 p18 p19 :=
  CheckedEuclid.step (q := [392, 329]) (r := p20)
    (by decide_cbv) tail19
private theorem tail17 : CheckedEuclid 1009 p17 p18 :=
  CheckedEuclid.step (q := [301, 200]) (r := p19)
    (by decide_cbv) tail18
private theorem tail16 : CheckedEuclid 1009 p16 p17 :=
  CheckedEuclid.step (q := [77, 833]) (r := p18)
    (by decide_cbv) tail17
private theorem tail15 : CheckedEuclid 1009 p15 p16 :=
  CheckedEuclid.step (q := [851, 389]) (r := p17)
    (by decide_cbv) tail16
private theorem tail14 : CheckedEuclid 1009 p14 p15 :=
  CheckedEuclid.step (q := [246, 188]) (r := p16)
    (by decide_cbv) tail15
private theorem tail13 : CheckedEuclid 1009 p13 p14 :=
  CheckedEuclid.step (q := [214, 412]) (r := p15)
    (by decide_cbv) tail14
private theorem tail12 : CheckedEuclid 1009 p12 p13 :=
  CheckedEuclid.step (q := [67, 276]) (r := p14)
    (by decide_cbv) tail13
private theorem tail11 : CheckedEuclid 1009 p11 p12 :=
  CheckedEuclid.step (q := [348, 6]) (r := p13)
    (by decide_cbv) tail12
private theorem tail10 : CheckedEuclid 1009 p10 p11 :=
  CheckedEuclid.step (q := [550, 333]) (r := p12)
    (by decide_cbv) tail11
private theorem tail9 : CheckedEuclid 1009 p9 p10 :=
  CheckedEuclid.step (q := [277, 976]) (r := p11)
    (by decide_cbv) tail10
private theorem tail8 : CheckedEuclid 1009 p8 p9 :=
  CheckedEuclid.step (q := [589, 36]) (r := p10)
    (by decide_cbv) tail9
private theorem tail7 : CheckedEuclid 1009 p7 p8 :=
  CheckedEuclid.step (q := [595, 864]) (r := p9)
    (by decide_cbv) tail8
private theorem tail6 : CheckedEuclid 1009 p6 p7 :=
  CheckedEuclid.step (q := [573, 845]) (r := p8)
    (by decide_cbv) tail7
private theorem tail5 : CheckedEuclid 1009 p5 p6 :=
  CheckedEuclid.step (q := [453, 856]) (r := p7)
    (by decide_cbv) tail6
private theorem tail4 : CheckedEuclid 1009 p4 p5 :=
  CheckedEuclid.step (q := [426, 876]) (r := p6)
    (by decide_cbv) tail5
private theorem tail3 : CheckedEuclid 1009 p3 p4 :=
  CheckedEuclid.step (q := [200, 919]) (r := p5)
    (by decide_cbv) tail4
private theorem tail2 : CheckedEuclid 1009 p2 p3 :=
  CheckedEuclid.step (q := [826, 147]) (r := p4)
    (by decide_cbv) tail3
private theorem tail1 : CheckedEuclid 1009 p1 p2 :=
  CheckedEuclid.step (q := [186, 153]) (r := p3)
    (by decide_cbv) tail2
private theorem tail0 : CheckedEuclid 1009 p0 p1 :=
  CheckedEuclid.step (q := [138, 267]) (r := p2)
    (by decide_cbv) tail1

theorem euclid : CheckedEuclid 1009 p0 p1 := tail0
theorem degreesPreserved : p0.length = 37 ∧ p1.length = 36 ∧
    p0.getLastD 0 % 1009 = 1 ∧ p1.getLastD 0 % 1009 = 325 := by decide

end Pair3

-- Expanded receipt: linear_s_pivot.
namespace Pair4

def p0 : List Nat := [631, 457, 44, 982, 23, 360, 378, 385, 115, 659, 254, 181, 93, 905, 686, 787, 798, 591, 793, 643, 428, 952, 792, 875, 735, 896, 615, 676, 355, 652, 134, 241, 433, 629, 945, 983, 1]
def p1 : List Nat := [615, 749, 337, 73, 528, 648, 696, 121, 328, 351, 224, 30, 747, 287, 469, 881, 942, 690, 79, 162, 492, 340, 289, 30, 664, 39, 275, 408, 385, 661, 259, 93, 357, 723, 34, 411]
def p2 : List Nat := [42, 916, 431, 401, 397, 523, 225, 192, 459, 11, 162, 986, 639, 591, 611, 5, 427, 613, 195, 725, 933, 271, 116, 35, 929, 215, 308, 545, 761, 210, 461, 491, 911, 1008, 85]
def p3 : List Nat := [245, 519, 75, 767, 984, 595, 745, 623, 301, 562, 63, 997, 123, 151, 498, 649, 381, 742, 203, 452, 926, 675, 579, 791, 134, 123, 657, 981, 887, 758, 657, 892, 516, 9]
def p4 : List Nat := [30, 532, 49, 881, 167, 762, 845, 214, 41, 936, 162, 58, 550, 4, 504, 783, 526, 284, 362, 476, 555, 475, 475, 457, 260, 653, 141, 626, 723, 479, 575, 877, 191]
def p5 : List Nat := [588, 438, 305, 387, 466, 399, 783, 646, 40, 636, 879, 248, 742, 386, 277, 234, 758, 795, 408, 411, 437, 178, 688, 896, 965, 709, 728, 621, 224, 514, 231, 501]
def p6 : List Nat := [978, 441, 783, 49, 972, 25, 139, 948, 126, 726, 951, 303, 145, 573, 229, 9, 886, 244, 214, 135, 502, 126, 549, 384, 303, 754, 799, 501, 667, 147, 601]
def p7 : List Nat := [219, 1008, 783, 900, 949, 817, 69, 356, 549, 530, 376, 464, 223, 890, 370, 355, 980, 120, 181, 133, 848, 629, 70, 193, 967, 669, 515, 702, 895, 685]
def p8 : List Nat := [291, 110, 711, 331, 225, 709, 43, 116, 360, 602, 45, 265, 851, 709, 220, 686, 1005, 330, 865, 226, 450, 907, 446, 789, 805, 866, 144, 127, 887]
def p9 : List Nat := [711, 856, 15, 931, 206, 821, 743, 95, 978, 949, 356, 386, 441, 439, 43, 456, 916, 951, 955, 609, 156, 574, 22, 430, 27, 321, 303, 698]
def p10 : List Nat := [471, 554, 182, 82, 565, 24, 246, 992, 650, 657, 107, 728, 52, 857, 2, 461, 176, 15, 974, 549, 600, 119, 88, 462, 345, 154, 163]
def p11 : List Nat := [652, 571, 638, 593, 616, 490, 522, 117, 737, 409, 512, 544, 139, 709, 626, 926, 711, 75, 844, 918, 111, 511, 691, 928, 280, 722]
def p12 : List Nat := [515, 994, 756, 572, 299, 188, 595, 215, 457, 933, 461, 599, 815, 325, 563, 60, 715, 982, 30, 982, 570, 723, 648, 286, 351]
def p13 : List Nat := [888, 572, 344, 799, 992, 246, 360, 87, 855, 658, 52, 567, 936, 9, 258, 905, 689, 955, 587, 433, 748, 338, 506, 398]
def p14 : List Nat := [549, 512, 35, 54, 596, 286, 583, 944, 964, 14, 741, 367, 536, 115, 688, 211, 33, 497, 573, 504, 712, 988, 417]
def p15 : List Nat := [70, 903, 540, 54, 567, 794, 132, 108, 866, 126, 334, 375, 266, 942, 251, 280, 953, 54, 121, 239, 325, 562]
def p16 : List Nat := [209, 444, 704, 814, 337, 501, 373, 144, 18, 325, 520, 583, 34, 676, 871, 900, 424, 701, 174, 436, 644]
def p17 : List Nat := [762, 501, 984, 949, 832, 910, 912, 95, 421, 582, 75, 514, 733, 249, 741, 703, 503, 764, 896, 851]
def p18 : List Nat := [925, 599, 989, 687, 346, 371, 397, 328, 665, 421, 896, 870, 790, 191, 798, 225, 264, 404, 595]
def p19 : List Nat := [64, 525, 952, 26, 819, 612, 441, 25, 511, 146, 594, 440, 149, 425, 85, 201, 925, 916]
def p20 : List Nat := [521, 25, 275, 740, 205, 763, 5, 817, 235, 394, 447, 835, 281, 887, 239, 667, 168]
def p21 : List Nat := [68, 986, 522, 368, 752, 638, 1006, 32, 964, 679, 262, 470, 598, 23, 35, 311]
def p22 : List Nat := [349, 531, 136, 878, 887, 928, 976, 485, 989, 15, 954, 106, 214, 443, 631]
def p23 : List Nat := [465, 878, 31, 508, 334, 334, 952, 515, 790, 96, 888, 0, 346, 198]
def p24 : List Nat := [858, 665, 831, 387, 970, 954, 12, 285, 598, 624, 502, 884, 992]
def p25 : List Nat := [785, 829, 394, 80, 370, 468, 523, 175, 854, 317, 240, 779]
def p26 : List Nat := [429, 321, 443, 523, 744, 727, 506, 573, 666, 779, 952]
def p27 : List Nat := [158, 945, 408, 920, 635, 182, 664, 173, 571, 907]
def p28 : List Nat := [467, 469, 63, 363, 611, 967, 1002, 792, 979]
def p29 : List Nat := [540, 822, 230, 479, 455, 389, 44, 766]
def p30 : List Nat := [817, 823, 858, 16, 853, 646, 260]
def p31 : List Nat := [935, 495, 358, 54, 885, 640]
def p32 : List Nat := [179, 749, 252, 14, 817]
def p33 : List Nat := [961, 804, 567, 524]
def p34 : List Nat := [367, 232, 107]
def p35 : List Nat := [856, 346]
def p36 : List Nat := [755]
def p37 : List Nat := []

private theorem tail36 : CheckedEuclid 1009 p36 p37 :=
  CheckedEuclid.done p36 (by decide) (by decide)
private theorem tail35 : CheckedEuclid 1009 p35 p36 :=
  CheckedEuclid.step (q := [664, 523]) (r := p37)
    (by decide_cbv) tail36
private theorem tail34 : CheckedEuclid 1009 p34 p35 :=
  CheckedEuclid.step (q := [174, 359]) (r := p36)
    (by decide_cbv) tail35
private theorem tail33 : CheckedEuclid 1009 p33 p34 :=
  CheckedEuclid.step (q := [146, 731]) (r := p35)
    (by decide_cbv) tail34
private theorem tail32 : CheckedEuclid 1009 p32 p33 :=
  CheckedEuclid.step (q := [88, 223]) (r := p34)
    (by decide_cbv) tail33
private theorem tail31 : CheckedEuclid 1009 p31 p32 :=
  CheckedEuclid.step (q := [603, 333]) (r := p33)
    (by decide_cbv) tail32
private theorem tail30 : CheckedEuclid 1009 p30 p31 :=
  CheckedEuclid.step (q := [155, 95]) (r := p32)
    (by decide_cbv) tail31
private theorem tail29 : CheckedEuclid 1009 p29 p30 :=
  CheckedEuclid.step (q := [701, 880]) (r := p31)
    (by decide_cbv) tail30
private theorem tail28 : CheckedEuclid 1009 p28 p29 :=
  CheckedEuclid.step (q := [317, 324]) (r := p30)
    (by decide_cbv) tail29
private theorem tail27 : CheckedEuclid 1009 p27 p28 :=
  CheckedEuclid.step (q := [64, 407]) (r := p29)
    (by decide_cbv) tail28
private theorem tail26 : CheckedEuclid 1009 p26 p27 :=
  CheckedEuclid.step (q := [715, 327]) (r := p28)
    (by decide_cbv) tail27
private theorem tail25 : CheckedEuclid 1009 p25 p26 :=
  CheckedEuclid.step (q := [700, 659]) (r := p27)
    (by decide_cbv) tail26
private theorem tail24 : CheckedEuclid 1009 p24 p25 :=
  CheckedEuclid.step (q := [417, 294]) (r := p26)
    (by decide_cbv) tail25
private theorem tail23 : CheckedEuclid 1009 p23 p24 :=
  CheckedEuclid.step (q := [383, 938]) (r := p25)
    (by decide_cbv) tail24
private theorem tail22 : CheckedEuclid 1009 p22 p23 :=
  CheckedEuclid.step (q := [511, 365]) (r := p24)
    (by decide_cbv) tail23
private theorem tail21 : CheckedEuclid 1009 p21 p22 :=
  CheckedEuclid.step (q := [898, 493]) (r := p23)
    (by decide_cbv) tail22
private theorem tail20 : CheckedEuclid 1009 p20 p21 :=
  CheckedEuclid.step (q := [418, 312]) (r := p22)
    (by decide_cbv) tail21
private theorem tail19 : CheckedEuclid 1009 p19 p20 :=
  CheckedEuclid.step (q := [703, 558]) (r := p21)
    (by decide_cbv) tail20
private theorem tail18 : CheckedEuclid 1009 p18 p19 :=
  CheckedEuclid.step (q := [700, 37]) (r := p20)
    (by decide_cbv) tail19
private theorem tail17 : CheckedEuclid 1009 p17 p18 :=
  CheckedEuclid.step (q := [304, 54]) (r := p19)
    (by decide_cbv) tail18
private theorem tail16 : CheckedEuclid 1009 p16 p17 :=
  CheckedEuclid.step (q := [248, 328]) (r := p18)
    (by decide_cbv) tail17
private theorem tail15 : CheckedEuclid 1009 p15 p16 :=
  CheckedEuclid.step (q := [16, 919]) (r := p17)
    (by decide_cbv) tail16
private theorem tail14 : CheckedEuclid 1009 p14 p15 :=
  CheckedEuclid.step (q := [149, 832]) (r := p16)
    (by decide_cbv) tail15
private theorem tail13 : CheckedEuclid 1009 p13 p14 :=
  CheckedEuclid.step (q := [880, 105]) (r := p15)
    (by decide_cbv) tail14
private theorem tail12 : CheckedEuclid 1009 p12 p13 :=
  CheckedEuclid.step (q := [584, 622]) (r := p14)
    (by decide_cbv) tail13
private theorem tail11 : CheckedEuclid 1009 p11 p12 :=
  CheckedEuclid.step (q := [458, 462]) (r := p13)
    (by decide_cbv) tail12
private theorem tail10 : CheckedEuclid 1009 p10 p11 :=
  CheckedEuclid.step (q := [588, 351]) (r := p12)
    (by decide_cbv) tail11
private theorem tail9 : CheckedEuclid 1009 p9 p10 :=
  CheckedEuclid.step (q := [947, 939]) (r := p11)
    (by decide_cbv) tail10
private theorem tail8 : CheckedEuclid 1009 p8 p9 :=
  CheckedEuclid.step (q := [434, 659]) (r := p10)
    (by decide_cbv) tail9
private theorem tail7 : CheckedEuclid 1009 p7 p8 :=
  CheckedEuclid.step (q := [456, 747]) (r := p9)
    (by decide_cbv) tail8
private theorem tail6 : CheckedEuclid 1009 p6 p7 :=
  CheckedEuclid.step (q := [169, 76]) (r := p8)
    (by decide_cbv) tail7
private theorem tail5 : CheckedEuclid 1009 p5 p6 :=
  CheckedEuclid.step (q := [932, 941]) (r := p7)
    (by decide_cbv) tail6
private theorem tail4 : CheckedEuclid 1009 p4 p5 :=
  CheckedEuclid.step (q := [472, 522]) (r := p6)
    (by decide_cbv) tail5
private theorem tail3 : CheckedEuclid 1009 p3 p4 :=
  CheckedEuclid.step (q := [224, 840]) (r := p5)
    (by decide_cbv) tail4
private theorem tail2 : CheckedEuclid 1009 p2 p3 :=
  CheckedEuclid.step (q := [729, 570]) (r := p4)
    (by decide_cbv) tail3
private theorem tail1 : CheckedEuclid 1009 p1 p2 :=
  CheckedEuclid.step (q := [201, 907]) (r := p3)
    (by decide_cbv) tail2
private theorem tail0 : CheckedEuclid 1009 p0 p1 :=
  CheckedEuclid.step (q := [713, 491]) (r := p2)
    (by decide_cbv) tail1

theorem euclid : CheckedEuclid 1009 p0 p1 := tail0
theorem degreesPreserved : p0.length = 37 ∧ p1.length = 36 ∧
    p0.getLastD 0 % 1009 = 1 ∧ p1.getLastD 0 % 1009 = 411 := by decide

end Pair4

-- Expanded receipt: same_clock_factor_one.
namespace Pair5

def p0 : List Nat := [631, 457, 44, 982, 23, 360, 378, 385, 115, 659, 254, 181, 93, 905, 686, 787, 798, 591, 793, 643, 428, 952, 792, 875, 735, 896, 615, 676, 355, 652, 134, 241, 433, 629, 945, 983, 1]
def p1 : List Nat := [394, 542, 715, 278, 322, 3, 406, 345, 461, 764, 21, 975, 444, 793, 827, 575, 674, 712, 291, 86, 313, 70, 701, 489, 15, 669, 95, 292, 553, 488, 317, 569, 973, 451, 576, 267]
def p2 : List Nat := [926, 249, 44, 921, 468, 743, 86, 670, 96, 989, 847, 665, 274, 971, 89, 163, 519, 981, 782, 1004, 424, 36, 35, 751, 708, 499, 506, 95, 692, 500, 443, 706, 0, 341, 128]
def p3 : List Nat := [345, 602, 771, 880, 968, 762, 725, 855, 369, 634, 184, 128, 464, 377, 86, 181, 45, 814, 699, 380, 242, 560, 30, 422, 819, 952, 236, 842, 587, 536, 45, 818, 935, 628]
def p4 : List Nat := [969, 799, 535, 305, 433, 281, 330, 956, 769, 717, 727, 611, 450, 218, 31, 496, 234, 406, 790, 151, 998, 803, 351, 571, 100, 840, 727, 760, 630, 341, 844, 927, 705]
def p5 : List Nat := [1008, 535, 836, 614, 341, 83, 509, 518, 321, 735, 981, 468, 348, 314, 531, 757, 858, 221, 193, 708, 719, 861, 296, 11, 434, 565, 610, 806, 39, 929, 995, 275]
def p6 : List Nat := [819, 992, 273, 259, 678, 556, 462, 502, 113, 53, 605, 583, 670, 232, 651, 117, 373, 481, 261, 590, 666, 352, 606, 710, 394, 657, 152, 759, 818, 826, 325]
def p7 : List Nat := [473, 989, 77, 714, 736, 744, 694, 887, 723, 999, 828, 652, 479, 384, 401, 795, 402, 886, 813, 204, 73, 394, 238, 227, 575, 756, 94, 529, 687, 896]
def p8 : List Nat := [143, 542, 723, 558, 10, 604, 360, 799, 728, 562, 700, 863, 122, 840, 741, 762, 77, 908, 622, 500, 32, 193, 634, 537, 322, 721, 330, 815, 252]
def p9 : List Nat := [73, 937, 71, 388, 234, 779, 1000, 773, 320, 822, 885, 428, 199, 107, 142, 166, 763, 353, 816, 5, 190, 3, 705, 491, 712, 608, 583, 404]
def p10 : List Nat := [770, 859, 265, 184, 348, 969, 329, 793, 1000, 386, 553, 861, 447, 731, 108, 649, 656, 424, 752, 583, 836, 106, 86, 390, 692, 500, 161]
def p11 : List Nat := [770, 86, 299, 308, 580, 535, 335, 376, 924, 681, 755, 802, 245, 398, 8, 908, 508, 505, 197, 628, 929, 285, 777, 896, 414, 720]
def p12 : List Nat := [706, 149, 561, 959, 330, 41, 295, 905, 514, 821, 866, 584, 935, 764, 503, 191, 125, 310, 391, 59, 497, 173, 565, 399, 111]
def p13 : List Nat := [450, 681, 50, 67, 327, 477, 864, 219, 842, 368, 173, 1, 407, 203, 79, 524, 987, 836, 972, 776, 891, 20, 503, 551]
def p14 : List Nat := [4, 201, 615, 920, 639, 602, 691, 446, 490, 669, 8, 659, 437, 33, 649, 746, 670, 635, 130, 240, 986, 775, 420]
def p15 : List Nat := [938, 828, 244, 330, 346, 341, 192, 173, 11, 455, 538, 370, 535, 732, 0, 910, 101, 719, 924, 168, 653, 386]
def p16 : List Nat := [288, 469, 594, 286, 67, 707, 493, 575, 676, 625, 963, 460, 247, 470, 689, 133, 426, 582, 796, 429, 732]
def p17 : List Nat := [596, 205, 301, 804, 810, 268, 913, 946, 453, 946, 975, 602, 342, 371, 270, 356, 361, 591, 288, 386]
def p18 : List Nat := [0, 220, 312, 188, 855, 822, 226, 991, 187, 805, 452, 142, 893, 65, 481, 749, 131, 671, 865]
def p19 : List Nat := [596, 705, 229, 814, 11, 243, 733, 56, 73, 167, 370, 419, 273, 60, 15, 62, 823, 295]
def p20 : List Nat := [434, 160, 501, 320, 201, 637, 727, 322, 100, 843, 497, 840, 130, 638, 238, 999, 538]
def p21 : List Nat := [57, 977, 766, 102, 371, 953, 889, 237, 150, 880, 421, 171, 1, 239, 94, 342]
def p22 : List Nat := [4, 949, 396, 39, 552, 110, 139, 971, 649, 642, 905, 652, 296, 403, 97]
def p23 : List Nat := [593, 506, 835, 936, 66, 765, 133, 116, 580, 1008, 95, 726, 54, 875]
def p24 : List Nat := [298, 101, 707, 1006, 510, 930, 759, 188, 350, 814, 588, 72, 968]
def p25 : List Nat := [954, 625, 182, 192, 854, 109, 16, 939, 102, 577, 743, 924]
def p26 : List Nat := [447, 134, 915, 179, 506, 853, 812, 671, 306, 229, 249]
def p27 : List Nat := [526, 77, 802, 505, 32, 415, 287, 242, 963, 975]
def p28 : List Nat := [391, 858, 713, 51, 711, 1003, 261, 687, 510]
def p29 : List Nat := [210, 67, 188, 640, 685, 187, 663, 211]
def p30 : List Nat := [64, 306, 237, 396, 42, 856, 719]
def p31 : List Nat := [967, 223, 279, 504, 198, 977]
def p32 : List Nat := [799, 694, 838, 588, 586]
def p33 : List Nat := [993, 650, 911, 603]
def p34 : List Nat := [791, 812, 748]
def p35 : List Nat := [486, 803]
def p36 : List Nat := [509]
def p37 : List Nat := []

private theorem tail36 : CheckedEuclid 1009 p36 p37 :=
  CheckedEuclid.done p36 (by decide) (by decide)
private theorem tail35 : CheckedEuclid 1009 p35 p36 :=
  CheckedEuclid.step (q := [108, 739]) (r := p37)
    (by decide_cbv) tail36
private theorem tail34 : CheckedEuclid 1009 p34 p35 :=
  CheckedEuclid.step (q := [312, 927]) (r := p36)
    (by decide_cbv) tail35
private theorem tail33 : CheckedEuclid 1009 p33 p34 :=
  CheckedEuclid.step (q := [604, 450]) (r := p35)
    (by decide_cbv) tail34
private theorem tail32 : CheckedEuclid 1009 p32 p33 :=
  CheckedEuclid.step (q := [504, 933]) (r := p34)
    (by decide_cbv) tail33
private theorem tail31 : CheckedEuclid 1009 p31 p32 :=
  CheckedEuclid.step (q := [77, 761]) (r := p33)
    (by decide_cbv) tail32
private theorem tail30 : CheckedEuclid 1009 p30 p31 :=
  CheckedEuclid.step (q := [522, 955]) (r := p32)
    (by decide_cbv) tail31
private theorem tail29 : CheckedEuclid 1009 p29 p30 :=
  CheckedEuclid.step (q := [67, 970]) (r := p31)
    (by decide_cbv) tail30
private theorem tail28 : CheckedEuclid 1009 p28 p29 :=
  CheckedEuclid.step (q := [852, 538]) (r := p30)
    (by decide_cbv) tail29
private theorem tail27 : CheckedEuclid 1009 p27 p28 :=
  CheckedEuclid.step (q := [55, 269]) (r := p29)
    (by decide_cbv) tail28
private theorem tail26 : CheckedEuclid 1009 p26 p27 :=
  CheckedEuclid.step (q := [73, 972]) (r := p28)
    (by decide_cbv) tail27
private theorem tail25 : CheckedEuclid 1009 p25 p26 :=
  CheckedEuclid.step (q := [247, 259]) (r := p27)
    (by decide_cbv) tail26
private theorem tail24 : CheckedEuclid 1009 p24 p25 :=
  CheckedEuclid.step (q := [443, 962]) (r := p26)
    (by decide_cbv) tail25
private theorem tail23 : CheckedEuclid 1009 p23 p24 :=
  CheckedEuclid.step (q := [957, 840]) (r := p25)
    (by decide_cbv) tail24
private theorem tail22 : CheckedEuclid 1009 p22 p23 :=
  CheckedEuclid.step (q := [219, 308]) (r := p24)
    (by decide_cbv) tail23
private theorem tail21 : CheckedEuclid 1009 p21 p22 :=
  CheckedEuclid.step (q := [875, 378]) (r := p23)
    (by decide_cbv) tail22
private theorem tail20 : CheckedEuclid 1009 p20 p21 :=
  CheckedEuclid.step (q := [574, 273]) (r := p22)
    (by decide_cbv) tail21
private theorem tail19 : CheckedEuclid 1009 p19 p20 :=
  CheckedEuclid.step (q := [343, 310]) (r := p21)
    (by decide_cbv) tail20
private theorem tail18 : CheckedEuclid 1009 p18 p19 :=
  CheckedEuclid.step (q := [497, 687]) (r := p20)
    (by decide_cbv) tail19
private theorem tail17 : CheckedEuclid 1009 p17 p18 :=
  CheckedEuclid.step (q := [915, 684]) (r := p19)
    (by decide_cbv) tail18
private theorem tail16 : CheckedEuclid 1009 p16 p17 :=
  CheckedEuclid.step (q := [549, 96]) (r := p18)
    (by decide_cbv) tail17
private theorem tail15 : CheckedEuclid 1009 p15 p16 :=
  CheckedEuclid.step (q := [821, 494]) (r := p17)
    (by decide_cbv) tail16
private theorem tail14 : CheckedEuclid 1009 p14 p15 :=
  CheckedEuclid.step (q := [4, 22]) (r := p16)
    (by decide_cbv) tail15
private theorem tail13 : CheckedEuclid 1009 p13 p14 :=
  CheckedEuclid.step (q := [887, 292]) (r := p15)
    (by decide_cbv) tail14
private theorem tail12 : CheckedEuclid 1009 p12 p13 :=
  CheckedEuclid.step (q := [163, 751]) (r := p14)
    (by decide_cbv) tail13
private theorem tail11 : CheckedEuclid 1009 p11 p12 :=
  CheckedEuclid.step (q := [615, 361]) (r := p13)
    (by decide_cbv) tail12
private theorem tail10 : CheckedEuclid 1009 p10 p11 :=
  CheckedEuclid.step (q := [595, 380]) (r := p12)
    (by decide_cbv) tail11
private theorem tail9 : CheckedEuclid 1009 p9 p10 :=
  CheckedEuclid.step (q := [252, 366]) (r := p11)
    (by decide_cbv) tail10
private theorem tail8 : CheckedEuclid 1009 p8 p9 :=
  CheckedEuclid.step (q := [489, 630]) (r := p10)
    (by decide_cbv) tail9
private theorem tail7 : CheckedEuclid 1009 p7 p8 :=
  CheckedEuclid.step (q := [659, 452]) (r := p9)
    (by decide_cbv) tail8
private theorem tail6 : CheckedEuclid 1009 p6 p7 :=
  CheckedEuclid.step (q := [443, 265]) (r := p8)
    (by decide_cbv) tail7
private theorem tail5 : CheckedEuclid 1009 p5 p6 :=
  CheckedEuclid.step (q := [661, 777]) (r := p7)
    (by decide_cbv) tail6
private theorem tail4 : CheckedEuclid 1009 p4 p5 :=
  CheckedEuclid.step (q := [859, 663]) (r := p6)
    (by decide_cbv) tail5
private theorem tail3 : CheckedEuclid 1009 p3 p4 :=
  CheckedEuclid.step (q := [849, 914]) (r := p5)
    (by decide_cbv) tail4
private theorem tail2 : CheckedEuclid 1009 p2 p3 :=
  CheckedEuclid.step (q := [810, 720]) (r := p4)
    (by decide_cbv) tail3
private theorem tail1 : CheckedEuclid 1009 p1 p2 :=
  CheckedEuclid.step (q := [899, 546]) (r := p3)
    (by decide_cbv) tail2
private theorem tail0 : CheckedEuclid 1009 p0 p1 :=
  CheckedEuclid.step (q := [304, 325]) (r := p2)
    (by decide_cbv) tail1

theorem euclid : CheckedEuclid 1009 p0 p1 := tail0
theorem degreesPreserved : p0.length = 37 ∧ p1.length = 36 ∧
    p0.getLastD 0 % 1009 = 1 ∧ p1.getLastD 0 % 1009 = 267 := by decide

end Pair5

-- Expanded receipt: same_clock_factor_two.
namespace Pair6

def p0 : List Nat := [631, 457, 44, 982, 23, 360, 378, 385, 115, 659, 254, 181, 93, 905, 686, 787, 798, 591, 793, 643, 428, 952, 792, 875, 735, 896, 615, 676, 355, 652, 134, 241, 433, 629, 945, 983, 1]
def p1 : List Nat := [173, 621, 127, 834, 966, 9, 209, 26, 374, 274, 63, 907, 323, 361, 463, 716, 4, 118, 873, 258, 939, 210, 85, 458, 45, 998, 285, 876, 650, 455, 951, 698, 901, 344, 719, 801]
def p2 : List Nat := [926, 180, 956, 921, 468, 743, 86, 670, 96, 989, 847, 665, 274, 971, 89, 163, 519, 981, 782, 1004, 424, 36, 35, 751, 708, 499, 506, 95, 692, 500, 443, 706, 0, 341, 128]
def p3 : List Nat := [26, 229, 587, 86, 886, 268, 157, 547, 98, 893, 552, 384, 383, 122, 258, 543, 135, 424, 79, 131, 726, 671, 90, 257, 439, 838, 708, 508, 752, 599, 135, 436, 787, 875]
def p4 : List Nat := [969, 722, 405, 279, 930, 281, 330, 956, 769, 717, 727, 611, 450, 218, 31, 496, 234, 406, 790, 151, 998, 803, 351, 571, 100, 840, 727, 760, 630, 341, 844, 927, 705]
def p5 : List Nat := [1006, 401, 184, 208, 103, 634, 518, 545, 963, 187, 925, 395, 35, 942, 584, 253, 556, 663, 579, 106, 139, 565, 888, 33, 293, 686, 821, 400, 117, 769, 967, 825]
def p6 : List Nat := [819, 246, 695, 285, 472, 137, 133, 502, 113, 53, 605, 583, 670, 232, 651, 117, 373, 481, 261, 590, 666, 352, 606, 710, 394, 657, 152, 759, 818, 826, 325]
def p7 : List Nat := [410, 878, 988, 502, 66, 971, 634, 702, 151, 979, 466, 947, 428, 143, 194, 367, 197, 640, 421, 612, 219, 173, 714, 681, 716, 250, 282, 578, 43, 670]
def p8 : List Nat := [143, 863, 569, 323, 196, 591, 679, 595, 225, 562, 700, 863, 122, 840, 741, 762, 77, 908, 622, 500, 32, 193, 634, 537, 322, 721, 330, 815, 252]
def p9 : List Nat := [219, 766, 313, 949, 957, 577, 980, 365, 675, 432, 637, 275, 597, 321, 426, 498, 271, 50, 430, 15, 570, 9, 97, 464, 118, 815, 740, 203]
def p10 : List Nat := [770, 536, 580, 877, 83, 198, 271, 667, 215, 286, 886, 861, 447, 731, 108, 649, 656, 424, 752, 583, 836, 106, 86, 390, 692, 500, 161]
def p11 : List Nat := [292, 241, 467, 689, 407, 906, 462, 710, 752, 178, 568, 12, 735, 185, 24, 706, 515, 506, 591, 875, 769, 855, 313, 670, 233, 142]
def p12 : List Nat := [706, 507, 866, 818, 591, 352, 726, 776, 268, 563, 892, 864, 466, 764, 503, 191, 125, 310, 391, 59, 497, 173, 565, 399, 111]
def p13 : List Nat := [341, 393, 768, 426, 749, 915, 121, 514, 791, 52, 214, 738, 264, 0, 237, 563, 943, 490, 898, 310, 655, 60, 500, 644]
def p14 : List Nat := [4, 408, 1008, 333, 231, 925, 530, 744, 149, 515, 127, 359, 149, 261, 743, 746, 670, 635, 130, 240, 986, 775, 420]
def p15 : List Nat := [796, 921, 180, 82, 432, 894, 300, 248, 909, 505, 165, 700, 636, 317, 152, 97, 303, 139, 754, 504, 950, 149]
def p16 : List Nat := [288, 742, 68, 249, 399, 601, 637, 904, 818, 575, 576, 570, 558, 892, 570, 511, 900, 582, 796, 429, 732]
def p17 : List Nat := [779, 665, 356, 391, 737, 790, 629, 949, 363, 449, 586, 291, 333, 338, 616, 529, 833, 560, 864, 149]
def p18 : List Nat := [0, 424, 414, 42, 330, 950, 501, 837, 885, 629, 50, 204, 937, 21, 124, 27, 36, 598, 330]
def p19 : List Nat := [779, 473, 212, 589, 228, 306, 992, 922, 598, 321, 19, 397, 134, 352, 599, 893, 489, 49]
def p20 : List Nat := [475, 155, 439, 231, 137, 369, 825, 239, 30, 635, 871, 741, 916, 637, 1004, 589, 242]
def p21 : List Nat := [119, 364, 293, 852, 786, 893, 760, 181, 186, 209, 524, 391, 512, 244, 220, 410]
def p22 : List Nat := [252, 59, 780, 693, 633, 910, 830, 46, 345, 942, 293, 843, 814, 296, 792]
def p23 : List Nat := [19, 810, 112, 693, 116, 645, 598, 25, 291, 160, 758, 18, 82, 562]
def p24 : List Nat := [44, 868, 602, 884, 890, 863, 405, 659, 911, 550, 329, 414, 676]
def p25 : List Nat := [780, 754, 550, 782, 581, 379, 421, 217, 781, 264, 561, 517]
def p26 : List Nat := [537, 363, 539, 101, 1006, 2, 636, 843, 916, 669, 912]
def p27 : List Nat := [572, 311, 687, 514, 737, 500, 701, 964, 506, 332]
def p28 : List Nat := [433, 436, 960, 103, 931, 235, 133, 97, 279]
def p29 : List Nat := [946, 193, 62, 381, 357, 875, 25, 586]
def p30 : List Nat := [639, 144, 140, 316, 888, 727, 458]
def p31 : List Nat := [268, 495, 256, 259, 711, 438]
def p32 : List Nat := [937, 82, 626, 773, 519]
def p33 : List Nat := [850, 308, 124, 155]
def p34 : List Nat := [407, 31, 212]
def p35 : List Nat := [326, 128]
def p36 : List Nat := [35]
def p37 : List Nat := []

private theorem tail36 : CheckedEuclid 1009 p36 p37 :=
  CheckedEuclid.done p36 (by decide) (by decide)
private theorem tail35 : CheckedEuclid 1009 p35 p36 :=
  CheckedEuclid.step (q := [903, 955]) (r := p37)
    (by decide_cbv) tail36
private theorem tail34 : CheckedEuclid 1009 p34 p35 :=
  CheckedEuclid.step (q := [973, 853]) (r := p36)
    (by decide_cbv) tail35
private theorem tail33 : CheckedEuclid 1009 p33 p34 :=
  CheckedEuclid.step (q := [807, 767]) (r := p35)
    (by decide_cbv) tail34
private theorem tail32 : CheckedEuclid 1009 p32 p33 :=
  CheckedEuclid.step (q := [333, 778]) (r := p34)
    (by decide_cbv) tail33
private theorem tail31 : CheckedEuclid 1009 p31 p32 :=
  CheckedEuclid.step (q := [933, 65]) (r := p33)
    (by decide_cbv) tail32
private theorem tail30 : CheckedEuclid 1009 p30 p31 :=
  CheckedEuclid.step (q := [910, 729]) (r := p32)
    (by decide_cbv) tail31
private theorem tail29 : CheckedEuclid 1009 p29 p30 :=
  CheckedEuclid.step (q := [849, 953]) (r := p31)
    (by decide_cbv) tail30
private theorem tail28 : CheckedEuclid 1009 p28 p29 :=
  CheckedEuclid.step (q := [740, 901]) (r := p30)
    (by decide_cbv) tail29
private theorem tail27 : CheckedEuclid 1009 p27 p28 :=
  CheckedEuclid.step (q := [859, 135]) (r := p29)
    (by decide_cbv) tail28
private theorem tail26 : CheckedEuclid 1009 p26 p27 :=
  CheckedEuclid.step (q := [734, 100]) (r := p28)
    (by decide_cbv) tail27
private theorem tail25 : CheckedEuclid 1009 p25 p26 :=
  CheckedEuclid.step (q := [410, 650]) (r := p27)
    (by decide_cbv) tail26
private theorem tail24 : CheckedEuclid 1009 p24 p25 :=
  CheckedEuclid.step (q := [901, 942]) (r := p26)
    (by decide_cbv) tail25
private theorem tail23 : CheckedEuclid 1009 p23 p24 :=
  CheckedEuclid.step (q := [556, 774]) (r := p25)
    (by decide_cbv) tail24
private theorem tail22 : CheckedEuclid 1009 p22 p23 :=
  CheckedEuclid.step (q := [542, 5]) (r := p24)
    (by decide_cbv) tail23
private theorem tail21 : CheckedEuclid 1009 p21 p22 :=
  CheckedEuclid.step (q := [609, 212]) (r := p23)
    (by decide_cbv) tail22
private theorem tail20 : CheckedEuclid 1009 p20 p21 :=
  CheckedEuclid.step (q := [960, 227]) (r := p22)
    (by decide_cbv) tail21
private theorem tail19 : CheckedEuclid 1009 p19 p20 :=
  CheckedEuclid.step (q := [713, 955]) (r := p21)
    (by decide_cbv) tail20
private theorem tail18 : CheckedEuclid 1009 p18 p19 :=
  CheckedEuclid.step (q := [24, 851]) (r := p20)
    (by decide_cbv) tail19
private theorem tail17 : CheckedEuclid 1009 p17 p18 :=
  CheckedEuclid.step (q := [781, 242]) (r := p19)
    (by decide_cbv) tail18
private theorem tail16 : CheckedEuclid 1009 p16 p17 :=
  CheckedEuclid.step (q := [183, 32]) (r := p18)
    (by decide_cbv) tail17
private theorem tail15 : CheckedEuclid 1009 p15 p16 :=
  CheckedEuclid.step (q := [445, 473]) (r := p17)
    (by decide_cbv) tail16
private theorem tail14 : CheckedEuclid 1009 p14 p15 :=
  CheckedEuclid.step (q := [674, 680]) (r := p16)
    (by decide_cbv) tail15
private theorem tail13 : CheckedEuclid 1009 p13 p14 :=
  CheckedEuclid.step (q := [643, 876]) (r := p15)
    (by decide_cbv) tail14
private theorem tail12 : CheckedEuclid 1009 p12 p13 :=
  CheckedEuclid.step (q := [727, 923]) (r := p14)
    (by decide_cbv) tail13
private theorem tail11 : CheckedEuclid 1009 p11 p12 :=
  CheckedEuclid.step (q := [836, 74]) (r := p13)
    (by decide_cbv) tail12
private theorem tail10 : CheckedEuclid 1009 p10 p11 :=
  CheckedEuclid.step (q := [871, 463]) (r := p12)
    (by decide_cbv) tail11
private theorem tail9 : CheckedEuclid 1009 p9 p10 :=
  CheckedEuclid.step (q := [756, 89]) (r := p11)
    (by decide_cbv) tail10
private theorem tail8 : CheckedEuclid 1009 p8 p9 :=
  CheckedEuclid.step (q := [163, 210]) (r := p10)
    (by decide_cbv) tail9
private theorem tail7 : CheckedEuclid 1009 p7 p8 :=
  CheckedEuclid.step (q := [968, 347]) (r := p9)
    (by decide_cbv) tail8
private theorem tail6 : CheckedEuclid 1009 p6 p7 :=
  CheckedEuclid.step (q := [484, 761]) (r := p8)
    (by decide_cbv) tail7
private theorem tail5 : CheckedEuclid 1009 p5 p6 :=
  CheckedEuclid.step (q := [974, 313]) (r := p7)
    (by decide_cbv) tail6
private theorem tail4 : CheckedEuclid 1009 p4 p5 :=
  CheckedEuclid.step (q := [959, 221]) (r := p6)
    (by decide_cbv) tail5
private theorem tail3 : CheckedEuclid 1009 p3 p4 :=
  CheckedEuclid.step (q := [529, 724]) (r := p5)
    (by decide_cbv) tail4
private theorem tail2 : CheckedEuclid 1009 p2 p3 :=
  CheckedEuclid.step (q := [270, 240]) (r := p4)
    (by decide_cbv) tail3
private theorem tail1 : CheckedEuclid 1009 p1 p2 :=
  CheckedEuclid.step (q := [679, 629]) (r := p3)
    (by decide_cbv) tail2
private theorem tail0 : CheckedEuclid 1009 p0 p1 :=
  CheckedEuclid.step (q := [774, 781]) (r := p2)
    (by decide_cbv) tail1

theorem euclid : CheckedEuclid 1009 p0 p1 := tail0
theorem degreesPreserved : p0.length = 37 ∧ p1.length = 36 ∧
    p0.getLastD 0 % 1009 = 1 ∧ p1.getLastD 0 % 1009 = 801 := by decide

end Pair6

-- Expanded receipt: two_row_clean_hull_pivot.
namespace Pair7

def p0 : List Nat := [631, 457, 44, 982, 23, 360, 378, 385, 115, 659, 254, 181, 93, 905, 686, 787, 798, 591, 793, 643, 428, 952, 792, 875, 735, 896, 615, 676, 355, 652, 134, 241, 433, 629, 945, 983, 1]
def p1 : List Nat := [529, 390, 260, 729, 549, 286, 836, 137, 609, 566, 416, 884, 510, 308, 182, 911, 353, 311, 746, 298, 725, 439, 260, 809, 538, 314, 901, 162, 733, 710, 983, 92, 82, 878, 306, 513]
def p2 : List Nat := [691, 806, 114, 749, 796, 779, 685, 455, 505, 205, 907, 348, 682, 302, 78, 763, 298, 978, 678, 58, 102, 567, 144, 632, 350, 927, 918, 802, 44, 937, 395, 559, 130, 198, 937]
def p3 : List Nat := [325, 883, 712, 513, 397, 32, 679, 700, 284, 381, 895, 509, 143, 197, 599, 457, 976, 87, 358, 773, 228, 906, 292, 508, 963, 285, 701, 159, 55, 568, 19, 564, 543, 156]
def p4 : List Nat := [843, 984, 898, 886, 315, 912, 592, 242, 489, 536, 539, 372, 40, 100, 536, 179, 568, 426, 423, 681, 227, 652, 618, 697, 60, 325, 980, 728, 407, 129, 101, 934, 399]
def p5 : List Nat := [160, 434, 252, 669, 361, 196, 600, 660, 317, 497, 976, 748, 618, 90, 245, 788, 520, 592, 791, 172, 866, 952, 383, 918, 138, 31, 416, 415, 451, 612, 691, 667]
def p6 : List Nat := [180, 705, 49, 697, 905, 933, 941, 99, 822, 774, 976, 488, 744, 385, 351, 874, 762, 833, 802, 580, 89, 55, 232, 699, 597, 717, 335, 324, 601, 751, 203]
def p7 : List Nat := [558, 993, 954, 289, 160, 501, 741, 569, 954, 776, 892, 68, 823, 811, 866, 129, 592, 393, 926, 533, 898, 597, 853, 207, 252, 265, 955, 146, 608, 671]
def p8 : List Nat := [760, 495, 563, 573, 652, 816, 277, 276, 950, 498, 63, 118, 492, 803, 477, 58, 283, 187, 439, 664, 189, 225, 731, 505, 150, 300, 691, 550, 746]
def p9 : List Nat := [640, 319, 171, 409, 513, 656, 248, 446, 650, 496, 556, 346, 662, 84, 171, 282, 907, 787, 112, 653, 926, 39, 376, 365, 95, 757, 199, 874]
def p10 : List Nat := [123, 405, 477, 177, 333, 97, 524, 89, 252, 458, 200, 976, 746, 957, 363, 717, 951, 586, 746, 223, 501, 411, 498, 907, 189, 657, 791]
def p11 : List Nat := [792, 582, 757, 861, 680, 347, 563, 939, 351, 12, 801, 271, 128, 177, 249, 38, 94, 239, 810, 487, 220, 654, 52, 248, 268, 240]
def p12 : List Nat := [451, 546, 594, 375, 736, 573, 881, 643, 372, 567, 350, 671, 545, 957, 805, 552, 868, 459, 619, 261, 359, 102, 578, 1007, 193]
def p13 : List Nat := [816, 67, 153, 315, 758, 221, 252, 695, 168, 120, 580, 317, 427, 187, 612, 117, 496, 756, 441, 968, 169, 244, 860, 136]
def p14 : List Nat := [782, 601, 995, 460, 913, 523, 128, 205, 129, 585, 321, 779, 690, 715, 914, 484, 505, 225, 760, 975, 989, 112, 1001]
def p15 : List Nat := [585, 540, 488, 594, 635, 188, 899, 546, 295, 108, 855, 975, 824, 141, 629, 248, 68, 809, 470, 123, 753, 258]
def p16 : List Nat := [647, 666, 132, 30, 756, 101, 10, 584, 419, 56, 905, 252, 790, 992, 118, 492, 642, 467, 596, 821, 875]
def p17 : List Nat := [942, 597, 868, 806, 236, 69, 723, 565, 898, 66, 620, 999, 385, 947, 309, 302, 797, 893, 334, 612]
def p18 : List Nat := [115, 42, 571, 662, 656, 823, 520, 373, 776, 788, 361, 349, 575, 656, 432, 136, 277, 252, 939]
def p19 : List Nat := [613, 190, 558, 134, 96, 948, 388, 492, 361, 985, 662, 413, 321, 277, 894, 723, 68, 87]
def p20 : List Nat := [862, 132, 180, 88, 297, 238, 709, 318, 139, 508, 967, 300, 961, 935, 211, 438, 256]
def p21 : List Nat := [149, 14, 90, 361, 75, 219, 27, 775, 422, 952, 823, 61, 499, 472, 755, 365]
def p22 : List Nat := [908, 110, 496, 220, 718, 948, 87, 493, 526, 335, 660, 754, 467, 804, 191]
def p23 : List Nat := [70, 856, 867, 933, 86, 436, 8, 404, 865, 672, 363, 967, 654, 68]
def p24 : List Nat := [45, 772, 853, 819, 926, 511, 953, 489, 339, 313, 815, 362, 366]
def p25 : List Nat := [746, 729, 236, 962, 816, 738, 505, 265, 224, 506, 995, 930]
def p26 : List Nat := [31, 407, 366, 778, 797, 984, 51, 540, 534, 636, 196]
def p27 : List Nat := [891, 179, 43, 406, 588, 705, 634, 939, 388, 781]
def p28 : List Nat := [723, 945, 190, 293, 257, 716, 786, 224, 875]
def p29 : List Nat := [356, 857, 733, 249, 674, 749, 788, 995]
def p30 : List Nat := [409, 927, 706, 855, 39, 715, 87]
def p31 : List Nat := [442, 296, 514, 236, 242, 716]
def p32 : List Nat := [838, 42, 144, 852, 32]
def p33 : List Nat := [402, 731, 524, 258]
def p34 : List Nat := [610, 831, 730]
def p35 : List Nat := [677, 23]
def p36 : List Nat := [125]
def p37 : List Nat := []

private theorem tail36 : CheckedEuclid 1009 p36 p37 :=
  CheckedEuclid.done p36 (by decide) (by decide)
private theorem tail35 : CheckedEuclid 1009 p35 p36 :=
  CheckedEuclid.step (q := [183, 428]) (r := p37)
    (by decide_cbv) tail36
private theorem tail34 : CheckedEuclid 1009 p34 p35 :=
  CheckedEuclid.step (q := [500, 953]) (r := p36)
    (by decide_cbv) tail35
private theorem tail33 : CheckedEuclid 1009 p33 p34 :=
  CheckedEuclid.step (q := [686, 509]) (r := p35)
    (by decide_cbv) tail34
private theorem tail32 : CheckedEuclid 1009 p32 p33 :=
  CheckedEuclid.step (q := [362, 532]) (r := p34)
    (by decide_cbv) tail33
private theorem tail31 : CheckedEuclid 1009 p31 p32 :=
  CheckedEuclid.step (q := [342, 653]) (r := p33)
    (by decide_cbv) tail32
private theorem tail30 : CheckedEuclid 1009 p30 p31 :=
  CheckedEuclid.step (q := [919, 165]) (r := p32)
    (by decide_cbv) tail31
private theorem tail29 : CheckedEuclid 1009 p29 p30 :=
  CheckedEuclid.step (q := [582, 197]) (r := p31)
    (by decide_cbv) tail30
private theorem tail28 : CheckedEuclid 1009 p28 p29 :=
  CheckedEuclid.step (q := [358, 442]) (r := p30)
    (by decide_cbv) tail29
private theorem tail27 : CheckedEuclid 1009 p27 p28 :=
  CheckedEuclid.step (q := [171, 77]) (r := p29)
    (by decide_cbv) tail28
private theorem tail26 : CheckedEuclid 1009 p26 p27 :=
  CheckedEuclid.step (q := [365, 601]) (r := p28)
    (by decide_cbv) tail27
private theorem tail25 : CheckedEuclid 1009 p25 p26 :=
  CheckedEuclid.step (q := [451, 118]) (r := p27)
    (by decide_cbv) tail26
private theorem tail24 : CheckedEuclid 1009 p24 p25 :=
  CheckedEuclid.step (q := [468, 72]) (r := p26)
    (by decide_cbv) tail25
private theorem tail23 : CheckedEuclid 1009 p23 p24 :=
  CheckedEuclid.step (q := [411, 127]) (r := p25)
    (by decide_cbv) tail24
private theorem tail22 : CheckedEuclid 1009 p22 p23 :=
  CheckedEuclid.step (q := [488, 77]) (r := p24)
    (by decide_cbv) tail23
private theorem tail21 : CheckedEuclid 1009 p21 p22 :=
  CheckedEuclid.step (q := [219, 97]) (r := p23)
    (by decide_cbv) tail22
private theorem tail20 : CheckedEuclid 1009 p20 p21 :=
  CheckedEuclid.step (q := [406, 971]) (r := p22)
    (by decide_cbv) tail21
private theorem tail19 : CheckedEuclid 1009 p19 p20 :=
  CheckedEuclid.step (q := [443, 225]) (r := p21)
    (by decide_cbv) tail20
private theorem tail18 : CheckedEuclid 1009 p18 p19 :=
  CheckedEuclid.step (q := [300, 985]) (r := p20)
    (by decide_cbv) tail19
private theorem tail17 : CheckedEuclid 1009 p17 p18 :=
  CheckedEuclid.step (q := [696, 539]) (r := p19)
    (by decide_cbv) tail18
private theorem tail16 : CheckedEuclid 1009 p16 p17 :=
  CheckedEuclid.step (q := [986, 102]) (r := p18)
    (by decide_cbv) tail17
private theorem tail15 : CheckedEuclid 1009 p15 p16 :=
  CheckedEuclid.step (q := [656, 736]) (r := p17)
    (by decide_cbv) tail16
private theorem tail14 : CheckedEuclid 1009 p14 p15 :=
  CheckedEuclid.step (q := [854, 876]) (r := p16)
    (by decide_cbv) tail15
private theorem tail13 : CheckedEuclid 1009 p13 p14 :=
  CheckedEuclid.step (q := [159, 992]) (r := p15)
    (by decide_cbv) tail14
private theorem tail12 : CheckedEuclid 1009 p12 p13 :=
  CheckedEuclid.step (q := [765, 1003]) (r := p14)
    (by decide_cbv) tail13
private theorem tail11 : CheckedEuclid 1009 p11 p12 :=
  CheckedEuclid.step (q := [868, 890]) (r := p13)
    (by decide_cbv) tail12
private theorem tail10 : CheckedEuclid 1009 p10 p11 :=
  CheckedEuclid.step (q := [234, 512]) (r := p12)
    (by decide_cbv) tail11
private theorem tail9 : CheckedEuclid 1009 p9 p10 :=
  CheckedEuclid.step (q := [89, 681]) (r := p11)
    (by decide_cbv) tail10
private theorem tail8 : CheckedEuclid 1009 p8 p9 :=
  CheckedEuclid.step (q := [485, 996]) (r := p10)
    (by decide_cbv) tail9
private theorem tail7 : CheckedEuclid 1009 p7 p8 :=
  CheckedEuclid.step (q := [130, 665]) (r := p9)
    (by decide_cbv) tail8
private theorem tail6 : CheckedEuclid 1009 p6 p7 :=
  CheckedEuclid.step (q := [885, 80]) (r := p8)
    (by decide_cbv) tail7
private theorem tail5 : CheckedEuclid 1009 p5 p6 :=
  CheckedEuclid.step (q := [9, 724]) (r := p7)
    (by decide_cbv) tail6
private theorem tail4 : CheckedEuclid 1009 p4 p5 :=
  CheckedEuclid.step (q := [969, 167]) (r := p6)
    (by decide_cbv) tail5
private theorem tail3 : CheckedEuclid 1009 p3 p4 :=
  CheckedEuclid.step (q := [309, 668]) (r := p5)
    (by decide_cbv) tail4
private theorem tail2 : CheckedEuclid 1009 p2 p3 :=
  CheckedEuclid.step (q := [785, 310]) (r := p4)
    (by decide_cbv) tail3
private theorem tail1 : CheckedEuclid 1009 p1 p2 :=
  CheckedEuclid.step (q := [323, 119]) (r := p3)
    (by decide_cbv) tail2
private theorem tail0 : CheckedEuclid 1009 p0 p1 :=
  CheckedEuclid.step (q := [883, 653]) (r := p2)
    (by decide_cbv) tail1

theorem euclid : CheckedEuclid 1009 p0 p1 := tail0
theorem degreesPreserved : p0.length = 37 ∧ p1.length = 36 ∧
    p0.getLastD 0 % 1009 = 1 ∧ p1.getLastD 0 % 1009 = 513 := by decide

end Pair7

-- Expanded receipt: quadratic_remainders.
namespace Pair8

def p0 : List Nat := [497, 96, 763, 481, 430, 218, 53, 761, 864]
def p1 : List Nat := [0, 512, 905, 779, 78, 222, 630, 21, 88, 222]
def p2 : List Nat := [497, 96, 763, 481, 430, 218, 53, 761, 864]
def p3 : List Nat := [256, 35, 667, 896, 335, 493, 57, 755]
def p4 : List Nat := [347, 115, 444, 906, 573, 308, 888]
def p5 : List Nat := [741, 715, 416, 155, 960, 41]
def p6 : List Nat := [370, 746, 622, 980, 443]
def p7 : List Nat := [442, 357, 1007, 714]
def p8 : List Nat := [532, 610, 329]
def p9 : List Nat := [440, 9]
def p10 : List Nat := [136]
def p11 : List Nat := []

private theorem tail10 : CheckedEuclid 1009 p10 p11 :=
  CheckedEuclid.done p10 (by decide) (by decide)
private theorem tail9 : CheckedEuclid 1009 p9 p10 :=
  CheckedEuclid.step (q := [300, 52]) (r := p11)
    (by decide_cbv) tail10
private theorem tail8 : CheckedEuclid 1009 p8 p9 :=
  CheckedEuclid.step (q := [909, 485]) (r := p10)
    (by decide_cbv) tail9
private theorem tail7 : CheckedEuclid 1009 p7 p8 :=
  CheckedEuclid.step (q := [899, 453]) (r := p9)
    (by decide_cbv) tail8
private theorem tail6 : CheckedEuclid 1009 p6 p7 :=
  CheckedEuclid.step (q := [721, 621]) (r := p8)
    (by decide_cbv) tail7
private theorem tail5 : CheckedEuclid 1009 p5 p6 :=
  CheckedEuclid.step (q := [898, 672]) (r := p7)
    (by decide_cbv) tail6
private theorem tail4 : CheckedEuclid 1009 p4 p5 :=
  CheckedEuclid.step (q := [546, 883]) (r := p6)
    (by decide_cbv) tail5
private theorem tail3 : CheckedEuclid 1009 p3 p4 :=
  CheckedEuclid.step (q := [932, 861]) (r := p5)
    (by decide_cbv) tail4
private theorem tail2 : CheckedEuclid 1009 p2 p3 :=
  CheckedEuclid.step (q := [40, 227]) (r := p4)
    (by decide_cbv) tail3
private theorem tail1 : CheckedEuclid 1009 p1 p2 :=
  CheckedEuclid.step (q := [505, 750]) (r := p3)
    (by decide_cbv) tail2
private theorem tail0 : CheckedEuclid 1009 p0 p1 :=
  CheckedEuclid.step (q := []) (r := p2)
    (by decide_cbv) tail1

theorem euclid : CheckedEuclid 1009 p0 p1 := tail0
theorem degreesPreserved : p0.length = 9 ∧ p1.length = 10 ∧
    p0.getLastD 0 % 1009 = 864 ∧ p1.getLastD 0 % 1009 = 222 := by decide

end Pair8

#print axioms certifyPrime
#print axioms Pair0.euclid
#print axioms Pair1.euclid
#print axioms Pair2.euclid
#print axioms Pair3.euclid
#print axioms Pair4.euclid
#print axioms Pair5.euclid
#print axioms Pair6.euclid
#print axioms Pair7.euclid
#print axioms Pair8.euclid

end RKResearch.Certified.Graded.OrderTwelveFifteen.UniformChartUnitArithmetic
