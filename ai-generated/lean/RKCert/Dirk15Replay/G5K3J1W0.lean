module
public import RKCert.Dirk15Replay.G5K3J1W0Part000
public import RKCert.Dirk15Replay.G5K3J1W0Part001
public import RKCert.Dirk15Replay.G5K3J1W0Part002
public import RKCert.Dirk15Replay.G5K3J1W0Part003
public import RKCert.Dirk15Replay.G5K3J1W0Part004
public import RKCert.Dirk15Replay.G5K3J1W0Part005

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.G5K3J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [668, 335, 85, 877, 705, 776, 209, 125, 218, 532, 994, 297, 419, 800, 157, 84, 354, 100, 592, 470, 826, 991, 928, 644, 539, 552, 117, 798, 978, 702, 897, 204, 736, 125, 139, 209, 590, 147, 216, 289, 473, 483, 445, 483, 811, 363, 105, 495, 813, 92, 516, 849, 168, 74, 316, 181, 620, 196, 774, 724, 600, 20, 488, 498, 975, 597, 746, 587, 79, 889, 129, 178, 448, 331, 130, 640, 825, 365, 801, 908, 929, 488, 899, 954, 163, 917, 145, 500, 118, 302, 789, 601, 643, 625, 231, 128, 418, 481, 480, 137, 641, 957, 611, 468, 256, 588, 106, 611, 549, 516, 607, 982, 945, 143, 58, 801, 847, 85, 582, 361, 49]
private def values : Fin 121 → Nat := fun i => (#[668, 828, 839, 91, 958, 841, 882, 426, 507, 122, 966, 471, 38, 161, 130, 857, 379, 476, 499, 224, 500, 200, 751, 604, 986, 786, 726, 114, 646, 639, 918, 908, 531, 559, 808, 55, 385, 898, 793, 496, 823, 946, 248, 16, 329, 976, 616, 489, 467, 259, 566, 242, 73, 913, 770, 112, 696, 519, 16, 235, 727, 191, 856, 910, 871, 557, 150, 417, 129, 802, 312, 195, 764, 613, 148, 107, 697, 702, 831, 356, 931, 34, 928, 678, 958, 524, 818, 368, 345, 12, 271, 709, 968, 726, 908, 677, 44, 898, 278, 477, 469, 390, 122, 902, 813, 1003, 746, 456, 308, 524, 460, 244, 557, 141, 420, 310, 918, 746, 581, 311, 1002] : Array Nat)[i.val]!

theorem exactReduction : (nodeGramNorm 5 3 1 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=120)
    (by decide) ((nodeGramNorm_degree (by decide) (by decide) 1 0).trans (by decide)) (by decide) values
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

end RKCert.FixedPolynomial.FixedReplay.G5K3J1W0
