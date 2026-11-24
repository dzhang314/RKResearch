module
public import RKCert.Dirk15Replay.T5K2J1W1Part000
public import RKCert.Dirk15Replay.T5K2J1W1Part001
public import RKCert.Dirk15Replay.T5K2J1W1Part002
public import RKCert.Dirk15Replay.T5K2J1W1Part003
public import RKCert.Dirk15Replay.T5K2J1W1Part004

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.T5K2J1W1
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [829, 997, 303, 382, 908, 507, 637, 181, 206, 165, 355, 795, 607, 93, 873, 586, 10, 800, 333, 747, 644, 779, 944, 578, 7, 511, 129, 879, 20, 624, 913, 949, 746, 791, 877, 645, 51, 382, 777, 126, 177, 326, 938, 762, 229, 861, 473, 443, 218, 352, 447, 666, 441, 346, 220, 982, 625, 944, 973, 244, 93, 326, 512, 746, 505, 634, 374, 741, 731, 826, 664, 430, 822, 743, 14, 324, 9, 763, 784, 169, 396, 854, 930, 861, 406, 869, 324, 895, 156, 256, 540, 809, 393, 523, 200, 518, 118, 967, 617, 281, 44]
private def values : Fin 101 → Nat := fun i => (#[829, 43, 749, 819, 450, 757, 939, 442, 298, 564, 446, 441, 352, 719, 659, 538, 444, 427, 90, 947, 608, 401, 793, 871, 400, 405, 137, 465, 686, 584, 258, 658, 280, 566, 76, 489, 817, 538, 38, 139, 31, 69, 112, 1002, 625, 988, 897, 815, 639, 682, 248, 321, 725, 556, 491, 89, 5, 705, 111, 763, 367, 521, 77, 386, 437, 844, 11, 46, 715, 202, 827, 743, 487, 725, 582, 152, 783, 564, 126, 770, 325, 650, 497, 108, 278, 284, 31, 741, 515, 475, 836, 165, 825, 175, 568, 905, 905, 672, 929, 232, 293] : Array Nat)[i.val]!

theorem exactReduction : (parameterGramNorm 5 2 1 1).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=100)
    (by decide) ((parameterGramNorm_degree 5 2 1 1).trans (by decide)) (by decide) values
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

end RKCert.FixedPolynomial.FixedReplay.T5K2J1W1
