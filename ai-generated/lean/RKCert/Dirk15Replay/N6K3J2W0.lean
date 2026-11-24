module
public import RKCert.Dirk15Replay.N6K3J2W0Part000
public import RKCert.Dirk15Replay.N6K3J2W0Part001
public import RKCert.Dirk15Replay.N6K3J2W0Part002
public import RKCert.Dirk15Replay.N6K3J2W0Part003
public import RKCert.Dirk15Replay.N6K3J2W0Part004
public import RKCert.Dirk15Replay.N6K3J2W0Part005

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N6K3J2W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [589, 695, 729, 762, 257, 996, 353, 489, 101, 866, 117, 278, 34, 948, 345, 464, 200, 732, 617, 574, 782, 7, 26, 861, 415, 845, 612, 336, 725, 791, 482, 198, 551, 836, 66, 168, 973, 183, 445, 965, 720, 654, 897, 964, 759, 936, 771, 689, 111, 579, 972, 519, 157, 380, 485, 382, 850, 151, 287, 55, 627, 953, 890, 1005, 309, 687, 316, 561, 203, 470, 639, 905, 193, 332, 213, 773, 730, 780, 485, 551, 364, 34, 536, 496, 437, 242, 719, 545, 454, 206, 53, 543, 871, 604, 928, 179, 386, 196, 853, 383, 880, 193, 28, 962, 534, 707, 818, 667, 432, 518, 894, 323, 927, 273, 297, 826, 602, 398, 651, 562, 603]
private def values : Fin 121 → Nat := fun i => (#[589, 910, 559, 476, 983, 849, 441, 303, 166, 368, 711, 14, 272, 941, 745, 45, 925, 696, 309, 831, 722, 960, 22, 862, 396, 414, 26, 743, 782, 768, 497, 602, 939, 742, 781, 165, 512, 968, 836, 298, 740, 122, 310, 825, 657, 669, 660, 157, 592, 296, 620, 168, 281, 541, 778, 22, 734, 1004, 913, 79, 125, 394, 417, 965, 804, 540, 7, 898, 128, 916, 187, 711, 804, 8, 919, 338, 558, 336, 136, 713, 997, 170, 234, 745, 970, 407, 772, 859, 527, 300, 609, 598, 412, 513, 919, 734, 897, 886, 846, 274, 276, 962, 1002, 182, 30, 596, 934, 119, 873, 342, 743, 222, 519, 888, 817, 840, 694, 611, 173, 579, 89] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 6 3 2 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=120)
    (by decide) ((nodeMomentNorm_degree (by decide) (by decide) 2 0).trans (by decide)) (by decide) values
  · intro i
    rw [eval_map]
    fin_cases i
    · exact At0.checked
    · exact At1.checked
    · exact At2.checked
    · exact At3.checked
    · exact At4.checked
    · exact At5.checked
    · exact At6.checked
    · exact At7.checked
    · exact At8.checked
    · exact At9.checked
    · exact At10.checked
    · exact At11.checked
    · exact At12.checked
    · exact At13.checked
    · exact At14.checked
    · exact At15.checked
    · exact At16.checked
    · exact At17.checked
    · exact At18.checked
    · exact At19.checked
    · exact At20.checked
    · exact At21.checked
    · exact At22.checked
    · exact At23.checked
    · exact At24.checked
    · exact At25.checked
    · exact At26.checked
    · exact At27.checked
    · exact At28.checked
    · exact At29.checked
    · exact At30.checked
    · exact At31.checked
    · exact At32.checked
    · exact At33.checked
    · exact At34.checked
    · exact At35.checked
    · exact At36.checked
    · exact At37.checked
    · exact At38.checked
    · exact At39.checked
    · exact At40.checked
    · exact At41.checked
    · exact At42.checked
    · exact At43.checked
    · exact At44.checked
    · exact At45.checked
    · exact At46.checked
    · exact At47.checked
    · exact At48.checked
    · exact At49.checked
    · exact At50.checked
    · exact At51.checked
    · exact At52.checked
    · exact At53.checked
    · exact At54.checked
    · exact At55.checked
    · exact At56.checked
    · exact At57.checked
    · exact At58.checked
    · exact At59.checked
    · exact At60.checked
    · exact At61.checked
    · exact At62.checked
    · exact At63.checked
    · exact At64.checked
    · exact At65.checked
    · exact At66.checked
    · exact At67.checked
    · exact At68.checked
    · exact At69.checked
    · exact At70.checked
    · exact At71.checked
    · exact At72.checked
    · exact At73.checked
    · exact At74.checked
    · exact At75.checked
    · exact At76.checked
    · exact At77.checked
    · exact At78.checked
    · exact At79.checked
    · exact At80.checked
    · exact At81.checked
    · exact At82.checked
    · exact At83.checked
    · exact At84.checked
    · exact At85.checked
    · exact At86.checked
    · exact At87.checked
    · exact At88.checked
    · exact At89.checked
    · exact At90.checked
    · exact At91.checked
    · exact At92.checked
    · exact At93.checked
    · exact At94.checked
    · exact At95.checked
    · exact At96.checked
    · exact At97.checked
    · exact At98.checked
    · exact At99.checked
    · exact At100.checked
    · exact At101.checked
    · exact At102.checked
    · exact At103.checked
    · exact At104.checked
    · exact At105.checked
    · exact At106.checked
    · exact At107.checked
    · exact At108.checked
    · exact At109.checked
    · exact At110.checked
    · exact At111.checked
    · exact At112.checked
    · exact At113.checked
    · exact At114.checked
    · exact At115.checked
    · exact At116.checked
    · exact At117.checked
    · exact At118.checked
    · exact At119.checked
    · exact At120.checked
  · decide +kernel

end RKCert.FixedPolynomial.FixedReplay.N6K3J2W0
