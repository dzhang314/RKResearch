module
public import RKCert.Dirk15Replay.N6K2J3W0Part000
public import RKCert.Dirk15Replay.N6K2J3W0Part001
public import RKCert.Dirk15Replay.N6K2J3W0Part002

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N6K2J3W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [706, 54, 426, 262, 782, 522, 161, 389, 408, 476, 315, 48, 241, 639, 448, 387, 337, 787, 470, 897, 616, 583, 458, 438, 793, 502, 341, 201, 230, 303, 563, 881, 784, 37, 451, 533, 31, 789, 5, 131, 682, 321, 429, 754, 762, 568, 998, 60, 35, 398, 534, 905, 476, 712, 998, 890, 961, 512, 334, 752, 497]
private def values : Fin 61 → Nat := fun i => (#[706, 742, 207, 769, 771, 840, 153, 588, 77, 452, 586, 898, 260, 977, 413, 438, 880, 24, 941, 622, 848, 552, 333, 571, 551, 592, 551, 736, 275, 868, 583, 113, 915, 315, 962, 173, 900, 566, 327, 374, 129, 295, 888, 228, 731, 274, 75, 802, 466, 620, 988, 648, 881, 105, 625, 322, 983, 28, 203, 68, 459] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 6 2 3 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=60)
    (by decide) ((nodeMomentNorm_degree (by decide) (by decide) 3 0).trans (by decide)) (by decide) values
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
  · decide +kernel

end RKCert.FixedPolynomial.FixedReplay.N6K2J3W0
