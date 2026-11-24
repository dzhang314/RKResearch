module
public import RKCert.Dirk15Replay.N5K3J1W1Part000
public import RKCert.Dirk15Replay.N5K3J1W1Part001
public import RKCert.Dirk15Replay.N5K3J1W1Part002

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N5K3J1W1
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [453, 669, 52, 382, 666, 335, 888, 934, 832, 758, 416, 788, 646, 705, 516, 383, 231, 951, 117, 117, 861, 723, 125, 722, 94, 569, 399, 355, 462, 209, 13, 333, 269, 936, 794, 339, 867, 223, 168, 1003, 10, 932, 104, 522, 875, 675, 714, 582, 612, 565, 643, 580, 171, 934, 241, 192, 626, 404, 2, 672, 712, 692, 992, 573, 677, 787, 220, 684, 878, 755, 768]
private def values : Fin 71 → Nat := fun i => (#[453, 764, 243, 296, 791, 109, 698, 258, 923, 583, 15, 355, 483, 410, 152, 821, 18, 572, 269, 15, 81, 701, 978, 737, 347, 39, 867, 402, 618, 371, 652, 84, 119, 727, 73, 212, 645, 851, 388, 119, 74, 922, 694, 726, 182, 936, 272, 846, 753, 178, 175, 90, 769, 731, 498, 924, 643, 1005, 890, 833, 261, 850, 577, 201, 634, 72, 541, 320, 115, 286, 607] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 5 3 1 1).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=70)
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
  · decide +kernel

end RKCert.FixedPolynomial.FixedReplay.N5K3J1W1
