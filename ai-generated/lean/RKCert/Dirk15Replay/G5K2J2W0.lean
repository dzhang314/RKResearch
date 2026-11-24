module
public import RKCert.Dirk15Replay.G5K2J2W0Part000
public import RKCert.Dirk15Replay.G5K2J2W0Part001
public import RKCert.Dirk15Replay.G5K2J2W0Part002
public import RKCert.Dirk15Replay.G5K2J2W0Part003

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.G5K2J2W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [60, 108, 913, 67, 83, 463, 517, 1002, 510, 654, 224, 293, 470, 190, 705, 30, 823, 954, 594, 481, 408, 64, 895, 201, 478, 236, 872, 601, 339, 53, 835, 42, 971, 678, 363, 313, 310, 856, 799, 39, 986, 127, 392, 795, 698, 927, 435, 318, 720, 109, 137, 50, 707, 985, 102, 201, 151, 631, 734, 972, 220, 963, 457, 480, 369, 476, 223, 751, 431, 540, 788, 551, 2, 250, 914, 207, 183, 693, 615, 370, 598]
private def values : Fin 81 → Nat := fun i => (#[60, 410, 801, 701, 447, 961, 651, 992, 271, 869, 832, 437, 548, 232, 667, 399, 568, 832, 845, 628, 893, 478, 208, 77, 159, 103, 403, 1007, 914, 811, 322, 115, 83, 289, 665, 396, 647, 978, 220, 582, 1002, 845, 633, 200, 749, 479, 619, 812, 732, 341, 383, 837, 467, 889, 222, 366, 245, 494, 552, 709, 289, 325, 589, 576, 81, 189, 566, 973, 30, 896, 295, 427, 834, 727, 954, 531, 641, 435, 516, 366, 871] : Array Nat)[i.val]!

theorem exactReduction : (nodeGramNorm 5 2 2 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=80)
    (by decide) ((nodeGramNorm_degree (by decide) (by decide) 2 0).trans (by decide)) (by decide) values
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

end RKCert.FixedPolynomial.FixedReplay.G5K2J2W0
