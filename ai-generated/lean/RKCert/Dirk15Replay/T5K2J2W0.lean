module
public import RKCert.Dirk15Replay.T5K2J2W0Part000
public import RKCert.Dirk15Replay.T5K2J2W0Part001
public import RKCert.Dirk15Replay.T5K2J2W0Part002
public import RKCert.Dirk15Replay.T5K2J2W0Part003

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.T5K2J2W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [54, 628, 12, 346, 862, 610, 367, 517, 286, 676, 363, 5, 443, 741, 899, 960, 546, 558, 40, 883, 234, 470, 243, 440, 185, 515, 264, 846, 383, 744, 669, 478, 640, 343, 560, 756, 365, 158, 993, 162, 693, 165, 391, 241, 650, 518, 75, 856, 508, 408, 105, 500, 476, 456, 82, 862, 105, 633, 167, 187, 870, 598, 220, 212, 925, 13, 615, 893, 751, 298, 450, 722, 507, 102, 400, 260, 744, 950, 497, 456, 16]
private def values : Fin 81 → Nat := fun i => (#[54, 488, 431, 852, 718, 443, 719, 408, 942, 29, 1, 264, 716, 272, 605, 756, 333, 487, 835, 95, 27, 401, 977, 302, 232, 282, 295, 665, 635, 124, 933, 293, 936, 797, 380, 771, 537, 308, 247, 788, 117, 648, 181, 95, 525, 951, 94, 112, 684, 53, 586, 270, 711, 409, 257, 720, 582, 390, 612, 112, 169, 33, 273, 736, 961, 755, 377, 568, 916, 249, 77, 568, 710, 396, 673, 729, 757, 71, 429, 824, 229] : Array Nat)[i.val]!

theorem exactReduction : (parameterGramNorm 5 2 2 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=80)
    (by decide) ((parameterGramNorm_degree 5 2 2 0).trans (by decide)) (by decide) values
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
  · decide +kernel

end RKCert.FixedPolynomial.FixedReplay.T5K2J2W0
