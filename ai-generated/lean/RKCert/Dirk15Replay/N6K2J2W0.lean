module
public import RKCert.Dirk15Replay.N6K2J2W0Part000
public import RKCert.Dirk15Replay.N6K2J2W0Part001
public import RKCert.Dirk15Replay.N6K2J2W0Part002

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N6K2J2W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [523, 294, 889, 203, 155, 439, 773, 73, 816, 75, 582, 291, 998, 274, 409, 269, 48, 886, 845, 769, 588, 938, 819, 287, 863, 447, 1000, 609, 861, 505, 263, 492, 158, 525, 785, 537, 204, 707, 526, 16, 821, 369, 469, 963, 784, 441, 183, 772, 540, 41, 665, 270, 420, 168, 884, 597, 556, 882, 427, 168, 578]
private def values : Fin 61 → Nat := fun i => (#[523, 460, 570, 287, 730, 587, 924, 840, 148, 776, 63, 93, 89, 577, 513, 293, 821, 516, 697, 356, 737, 447, 813, 935, 122, 780, 757, 45, 385, 973, 318, 52, 69, 105, 826, 498, 929, 576, 885, 137, 782, 849, 170, 868, 661, 341, 786, 986, 889, 259, 452, 547, 329, 575, 795, 913, 480, 380, 539, 29, 128] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 6 2 2 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=60)
    (by decide) ((nodeMomentNorm_degree (by decide) (by decide) 2 0).trans (by decide)) (by decide) values
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

end RKCert.FixedPolynomial.FixedReplay.N6K2J2W0
