module
public import RKCert.Dirk15Replay.T5K2J1W0Part000
public import RKCert.Dirk15Replay.T5K2J1W0Part001
public import RKCert.Dirk15Replay.T5K2J1W0Part002
public import RKCert.Dirk15Replay.T5K2J1W0Part003

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.T5K2J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [252, 761, 374, 438, 625, 444, 394, 837, 780, 868, 172, 281, 978, 350, 194, 683, 179, 283, 553, 891, 757, 264, 659, 922, 1008, 612, 503, 344, 515, 15, 931, 776, 428, 282, 724, 372, 570, 917, 148, 620, 574, 187, 962, 165, 312, 809, 854, 743, 714, 880, 58, 227, 842, 414, 151, 36, 890, 986, 760, 534, 391, 61, 988, 234, 92, 270, 895, 187, 8, 782, 615, 661, 316, 798, 783, 103, 563, 227, 234, 56, 963]
private def values : Fin 81 → Nat := fun i => (#[252, 660, 554, 448, 815, 948, 407, 293, 467, 59, 380, 768, 604, 566, 744, 49, 283, 759, 195, 517, 518, 471, 61, 780, 164, 618, 64, 978, 297, 390, 506, 636, 870, 708, 759, 924, 3, 433, 98, 366, 885, 703, 495, 165, 277, 430, 872, 549, 441, 527, 446, 9, 200, 945, 976, 838, 686, 781, 948, 981, 90, 781, 887, 503, 416, 511, 432, 923, 494, 542, 775, 256, 367, 142, 62, 241, 941, 311, 847, 649, 393] : Array Nat)[i.val]!

theorem exactReduction : (parameterGramNorm 5 2 1 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=80)
    (by decide) ((parameterGramNorm_degree 5 2 1 0).trans (by decide)) (by decide) values
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

end RKCert.FixedPolynomial.FixedReplay.T5K2J1W0
