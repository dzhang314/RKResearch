module
public import RKCert.Dirk15Replay.T6K2J2W0Part000
public import RKCert.Dirk15Replay.T6K2J2W0Part001
public import RKCert.Dirk15Replay.T6K2J2W0Part002
public import RKCert.Dirk15Replay.T6K2J2W0Part003
public import RKCert.Dirk15Replay.T6K2J2W0Part004
public import RKCert.Dirk15Replay.T6K2J2W0Part005

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.T6K2J2W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [761, 437, 30, 573, 620, 95, 244, 389, 931, 591, 891, 213, 695, 365, 817, 75, 458, 107, 158, 94, 232, 877, 577, 791, 560, 543, 11, 162, 567, 797, 344, 661, 924, 134, 328, 54, 908, 663, 846, 997, 579, 373, 731, 495, 153, 794, 258, 107, 62, 325, 280, 713, 225, 918, 793, 279, 537, 621, 96, 400, 48, 842, 409, 960, 531, 327, 896, 4, 983, 263, 887, 167, 753, 885, 211, 723, 693, 980, 796, 1007, 478, 563, 309, 243, 340, 338, 341, 976, 226, 401, 276, 259, 484, 642, 933, 341, 406, 957, 888, 81, 52, 914, 215, 76, 816, 165, 146, 650, 477, 522, 132, 983, 671, 24, 946, 903, 20, 776, 468, 536, 223]
private def values : Fin 121 → Nat := fun i => (#[761, 290, 300, 670, 788, 441, 659, 103, 487, 895, 62, 553, 228, 662, 972, 890, 558, 227, 97, 333, 401, 173, 294, 795, 179, 672, 702, 572, 723, 124, 1004, 164, 172, 400, 872, 792, 778, 980, 244, 18, 709, 780, 974, 450, 785, 526, 181, 261, 197, 397, 924, 301, 291, 819, 3, 797, 388, 109, 369, 526, 889, 717, 736, 544, 15, 374, 253, 873, 253, 725, 677, 801, 304, 172, 98, 884, 771, 53, 884, 681, 218, 312, 743, 616, 994, 705, 2, 370, 153, 937, 232, 980, 73, 101, 738, 818, 104, 747, 322, 869, 348, 259, 283, 172, 762, 901, 167, 135, 387, 218, 587, 874, 981, 20, 771, 966, 321, 384, 50, 285, 580] : Array Nat)[i.val]!

theorem exactReduction : (parameterGramNorm 6 2 2 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=120)
    (by decide) ((parameterGramNorm_degree 6 2 2 0).trans (by decide)) (by decide) values
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

end RKCert.FixedPolynomial.FixedReplay.T6K2J2W0
