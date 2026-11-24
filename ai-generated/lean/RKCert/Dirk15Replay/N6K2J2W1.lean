module
public import RKCert.Dirk15Replay.N6K2J2W1Part000
public import RKCert.Dirk15Replay.N6K2J2W1Part001
public import RKCert.Dirk15Replay.N6K2J2W1Part002
public import RKCert.Dirk15Replay.N6K2J2W1Part003

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N6K2J2W1
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [523, 212, 730, 851, 1004, 647, 24, 201, 469, 414, 509, 256, 866, 455, 736, 581, 446, 482, 851, 91, 191, 930, 386, 644, 541, 624, 903, 243, 457, 332, 902, 121, 984, 170, 558, 566, 95, 713, 178, 46, 282, 124, 89, 824, 467, 403, 57, 186, 236, 381, 660, 591, 761, 34, 679, 891, 208, 109, 896, 980, 925, 749, 893, 935, 999, 729, 869, 775, 529, 37, 888, 276, 63, 469, 122, 512]
private def values : Fin 76 → Nat := fun i => (#[523, 218, 432, 166, 834, 359, 470, 165, 338, 598, 841, 227, 309, 158, 477, 899, 793, 952, 979, 889, 348, 456, 462, 847, 399, 914, 317, 253, 826, 407, 369, 694, 28, 504, 682, 156, 868, 363, 220, 817, 144, 541, 157, 11, 266, 707, 601, 372, 285, 519, 623, 769, 396, 80, 815, 558, 493, 414, 901, 361, 453, 943, 260, 61, 754, 664, 477, 721, 901, 407, 169, 231, 321, 699, 955, 448] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 6 2 2 1).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=75)
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
    · exact At71.checked
    · exact At72.checked
    · exact At73.checked
    · exact At74.checked
    · exact At75.checked
  · decide +kernel

end RKCert.FixedPolynomial.FixedReplay.N6K2J2W1
