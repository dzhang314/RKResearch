module
public import RKCert.Dirk15Replay.N5K3J2W1Part000
public import RKCert.Dirk15Replay.N5K3J2W1Part001
public import RKCert.Dirk15Replay.N5K3J2W1Part002

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N5K3J2W1
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [302, 620, 57, 629, 265, 263, 110, 493, 412, 241, 947, 392, 453, 104, 832, 464, 120, 853, 27, 617, 975, 557, 565, 837, 433, 535, 223, 536, 850, 457, 78, 508, 260, 83, 264, 686, 816, 224, 910, 245, 896, 950, 732, 714, 922, 843, 410, 201, 417, 18, 871, 879, 532, 996, 983, 934, 476, 925, 161, 127, 433, 1002, 568, 160, 208, 503, 908, 727, 788, 102, 961]
private def values : Fin 71 → Nat := fun i => (#[302, 257, 265, 754, 942, 820, 222, 253, 994, 965, 585, 874, 222, 512, 173, 104, 476, 603, 146, 484, 361, 293, 202, 503, 325, 733, 500, 697, 625, 517, 668, 994, 568, 450, 128, 413, 727, 1006, 843, 201, 820, 417, 594, 654, 587, 549, 110, 533, 515, 570, 308, 514, 515, 575, 119, 277, 402, 81, 674, 409, 333, 441, 25, 611, 915, 239, 715, 207, 94, 489, 138] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 5 3 2 1).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=70)
    (by decide) ((nodeMomentNorm_degree (by decide) (by decide) 2 1).trans (by decide)) (by decide) values
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
  · decide +kernel

end RKCert.FixedPolynomial.FixedReplay.N5K3J2W1
