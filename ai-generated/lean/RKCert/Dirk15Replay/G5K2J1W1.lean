module
public import RKCert.Dirk15Replay.G5K2J1W1Part000
public import RKCert.Dirk15Replay.G5K2J1W1Part001
public import RKCert.Dirk15Replay.G5K2J1W1Part002
public import RKCert.Dirk15Replay.G5K2J1W1Part003
public import RKCert.Dirk15Replay.G5K2J1W1Part004

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.G5K2J1W1
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [740, 390, 622, 473, 197, 101, 286, 198, 306, 139, 585, 424, 554, 540, 588, 726, 158, 288, 507, 628, 1, 187, 220, 830, 194, 705, 505, 753, 428, 412, 618, 581, 22, 495, 510, 865, 175, 661, 16, 435, 483, 586, 668, 77, 413, 212, 445, 931, 413, 230, 304, 625, 992, 537, 329, 958, 682, 465, 398, 448, 489, 770, 244, 884, 38, 871, 737, 367, 403, 951, 245, 852, 200, 911, 478, 584, 874, 22, 681, 835, 732, 56, 848, 364, 104, 173, 739, 716, 430, 262, 870, 494, 558, 766, 852, 957, 1005, 125, 646, 592, 598]
private def values : Fin 101 → Nat := fun i => (#[740, 132, 47, 219, 744, 238, 570, 364, 150, 326, 506, 348, 206, 355, 169, 770, 692, 200, 594, 148, 131, 122, 179, 412, 335, 308, 943, 774, 854, 53, 65, 778, 360, 426, 948, 669, 752, 951, 717, 948, 123, 554, 449, 469, 224, 83, 6, 283, 161, 769, 263, 484, 342, 159, 376, 674, 201, 709, 734, 58, 82, 3, 788, 335, 84, 602, 502, 945, 473, 38, 1003, 583, 280, 842, 207, 825, 972, 765, 878, 990, 590, 341, 15, 317, 35, 264, 988, 680, 131, 896, 605, 1002, 788, 786, 454, 782, 317, 773, 277, 475, 250] : Array Nat)[i.val]!

theorem exactReduction : (nodeGramNorm 5 2 1 1).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=100)
    (by decide) ((nodeGramNorm_degree (by decide) (by decide) 1 1).trans (by decide)) (by decide) values
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
  · decide +kernel

end RKCert.FixedPolynomial.FixedReplay.G5K2J1W1
