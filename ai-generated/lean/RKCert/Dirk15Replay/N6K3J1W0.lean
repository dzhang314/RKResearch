module
public import RKCert.Dirk15Replay.N6K3J1W0Part000
public import RKCert.Dirk15Replay.N6K3J1W0Part001
public import RKCert.Dirk15Replay.N6K3J1W0Part002
public import RKCert.Dirk15Replay.N6K3J1W0Part003
public import RKCert.Dirk15Replay.N6K3J1W0Part004
public import RKCert.Dirk15Replay.N6K3J1W0Part005

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N6K3J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [64, 192, 387, 845, 614, 830, 471, 365, 536, 697, 933, 210, 814, 928, 107, 24, 316, 898, 848, 339, 266, 840, 388, 436, 778, 89, 172, 600, 108, 895, 145, 191, 521, 399, 883, 983, 35, 312, 757, 936, 270, 581, 203, 472, 88, 545, 128, 114, 819, 675, 754, 735, 456, 876, 1005, 644, 210, 782, 813, 149, 732, 314, 1003, 460, 598, 917, 784, 313, 31, 179, 492, 182, 604, 267, 703, 0, 194, 23, 53, 731, 660, 771, 357, 217, 34, 587, 544, 792, 200, 88, 113, 875, 330, 446, 601, 0, 173, 199, 834, 57, 416, 660, 212, 81, 558, 22, 405, 250, 337, 309, 441, 846, 177, 375, 470, 345, 140, 323, 792, 961, 494]
private def values : Fin 121 → Nat := fun i => (#[64, 48, 716, 955, 199, 161, 869, 876, 795, 746, 752, 555, 103, 768, 820, 735, 394, 583, 737, 419, 328, 962, 64, 189, 209, 72, 1000, 838, 368, 861, 942, 666, 110, 926, 968, 573, 340, 283, 594, 711, 111, 334, 534, 815, 840, 836, 628, 761, 454, 769, 488, 357, 276, 30, 200, 198, 854, 88, 137, 457, 759, 333, 735, 211, 247, 486, 672, 835, 218, 584, 544, 18, 555, 64, 549, 498, 376, 490, 225, 615, 996, 490, 113, 881, 388, 74, 895, 604, 682, 796, 715, 468, 296, 881, 574, 862, 472, 689, 819, 832, 334, 442, 59, 561, 872, 656, 63, 123, 580, 302, 855, 695, 941, 449, 184, 472, 566, 499, 969, 876, 618] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 6 3 1 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=120)
    (by decide) ((nodeMomentNorm_degree (by decide) (by decide) 1 0).trans (by decide)) (by decide) values
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

end RKCert.FixedPolynomial.FixedReplay.N6K3J1W0
