module
public import RKCert.Dirk15Replay.G5K2J1W0Part000
public import RKCert.Dirk15Replay.G5K2J1W0Part001
public import RKCert.Dirk15Replay.G5K2J1W0Part002
public import RKCert.Dirk15Replay.G5K2J1W0Part003

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.G5K2J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [740, 189, 504, 816, 813, 805, 352, 924, 643, 391, 473, 823, 338, 774, 324, 321, 824, 244, 685, 916, 662, 4, 117, 506, 306, 719, 131, 421, 369, 425, 696, 141, 526, 958, 530, 638, 454, 694, 311, 894, 782, 108, 134, 506, 113, 860, 578, 284, 628, 464, 504, 176, 405, 700, 204, 120, 165, 987, 386, 181, 173, 964, 571, 961, 154, 70, 24, 628, 62, 114, 213, 463, 332, 644, 528, 389, 101, 889, 905, 748, 213]
private def values : Fin 81 → Nat := fun i => (#[740, 490, 636, 411, 923, 762, 382, 565, 740, 262, 206, 924, 346, 561, 746, 60, 684, 863, 63, 803, 160, 888, 1, 660, 746, 566, 270, 449, 995, 741, 594, 704, 674, 553, 1, 103, 722, 443, 920, 26, 946, 301, 13, 268, 122, 766, 231, 925, 342, 442, 694, 780, 1, 360, 691, 29, 700, 341, 267, 693, 139, 670, 750, 848, 91, 743, 99, 553, 783, 232, 612, 643, 1, 692, 123, 666, 280, 421, 458, 949, 846] : Array Nat)[i.val]!

theorem exactReduction : (nodeGramNorm 5 2 1 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=80)
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
  · decide +kernel

end RKCert.FixedPolynomial.FixedReplay.G5K2J1W0
