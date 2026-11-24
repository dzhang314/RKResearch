module
public import RKCert.Dirk15Replay.N6K2J1W0Part000
public import RKCert.Dirk15Replay.N6K2J1W0Part001
public import RKCert.Dirk15Replay.N6K2J1W0Part002

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N6K2J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [865, 793, 196, 546, 919, 232, 498, 34, 265, 828, 449, 48, 217, 291, 954, 116, 55, 711, 475, 4, 34, 703, 525, 6, 144, 769, 444, 373, 409, 193, 836, 291, 803, 855, 695, 25, 279, 285, 828, 686, 268, 34, 928, 622, 305, 750, 356, 981, 929, 103, 374, 862, 32, 394, 31, 994, 532, 198, 235, 302, 222]
private def values : Fin 61 → Nat := fun i => (#[865, 897, 805, 882, 39, 1005, 812, 859, 206, 563, 504, 912, 529, 155, 743, 353, 439, 474, 410, 215, 474, 359, 178, 316, 916, 943, 902, 310, 904, 85, 495, 347, 953, 731, 790, 172, 517, 378, 295, 997, 201, 728, 23, 895, 939, 978, 232, 9, 119, 948, 153, 129, 10, 237, 474, 618, 379, 736, 524, 858, 314] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 6 2 1 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=60)
    (by decide) ((nodeMomentNorm_degree (by decide) (by decide) 1 0).trans (by decide)) (by decide) values
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

end RKCert.FixedPolynomial.FixedReplay.N6K2J1W0
