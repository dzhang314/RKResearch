module
public import RKCert.Dirk15Replay.N6K2J1W1Part000
public import RKCert.Dirk15Replay.N6K2J1W1Part001
public import RKCert.Dirk15Replay.N6K2J1W1Part002
public import RKCert.Dirk15Replay.N6K2J1W1Part003

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N6K2J1W1
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [865, 215, 890, 698, 300, 895, 392, 303, 48, 247, 336, 72, 950, 755, 818, 203, 7, 979, 298, 671, 195, 962, 521, 534, 714, 970, 670, 782, 386, 461, 481, 703, 881, 760, 522, 451, 879, 495, 205, 865, 111, 983, 266, 494, 295, 755, 560, 856, 807, 943, 268, 883, 690, 235, 876, 463, 972, 880, 797, 368, 98, 309, 1006, 666, 148, 962, 219, 207, 89, 637, 203, 874, 981, 72, 75, 431]
private def values : Fin 76 → Nat := fun i => (#[865, 489, 117, 810, 25, 127, 803, 604, 362, 689, 808, 873, 942, 323, 573, 189, 141, 467, 490, 767, 273, 260, 382, 705, 619, 121, 919, 972, 767, 37, 323, 33, 784, 868, 589, 374, 742, 635, 703, 108, 879, 47, 474, 993, 566, 1001, 789, 461, 750, 484, 218, 157, 906, 938, 55, 339, 126, 813, 258, 596, 141, 767, 507, 87, 149, 804, 365, 638, 842, 106, 649, 578, 119, 86, 361, 311] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 6 2 1 1).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=75)
    (by decide) ((nodeMomentNorm_degree (by decide) (by decide) 1 1).trans (by decide)) (by decide) values
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
  · decide +kernel

end RKCert.FixedPolynomial.FixedReplay.N6K2J1W1
