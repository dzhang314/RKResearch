module
public import RKCert.Dirk15Replay.N6K4J1W0Part000
public import RKCert.Dirk15Replay.N6K4J1W0Part001
public import RKCert.Dirk15Replay.N6K4J1W0Part002
public import RKCert.Dirk15Replay.N6K4J1W0Part003
public import RKCert.Dirk15Replay.N6K4J1W0Part004
public import RKCert.Dirk15Replay.N6K4J1W0Part005

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N6K4J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [557, 662, 192, 970, 15, 349, 866, 549, 678, 474, 837, 916, 792, 125, 729, 268, 601, 184, 56, 575, 557, 214, 338, 761, 367, 285, 523, 609, 986, 326, 177, 317, 149, 788, 29, 631, 638, 100, 901, 145, 557, 503, 81, 286, 780, 709, 922, 907, 580, 413, 863, 617, 953, 929, 791, 214, 727, 563, 841, 443, 630, 368, 300, 183, 536, 798, 902, 996, 693, 361, 721, 705, 604, 514, 230, 30, 362, 266, 251, 244, 596, 846, 940, 32, 678, 719, 490, 725, 787, 319, 643, 713, 323, 597, 687, 4, 722, 158, 749, 355, 905, 696, 837, 565, 544, 660, 999, 441, 989, 710, 451, 613, 192, 888, 977, 202, 520, 884, 233, 485, 436]
private def values : Fin 121 → Nat := fun i => (#[557, 334, 845, 732, 185, 41, 659, 630, 1008, 220, 73, 225, 841, 947, 184, 963, 219, 644, 630, 496, 330, 855, 466, 374, 409, 501, 335, 162, 458, 532, 831, 326, 510, 120, 271, 302, 925, 378, 892, 391, 37, 844, 579, 56, 136, 1006, 423, 796, 846, 863, 44, 819, 208, 261, 297, 709, 470, 276, 288, 963, 608, 746, 247, 612, 157, 24, 930, 766, 303, 958, 43, 726, 136, 559, 103, 670, 223, 221, 988, 144, 204, 306, 517, 255, 178, 442, 210, 558, 354, 184, 577, 125, 936, 768, 102, 167, 848, 96, 938, 884, 505, 239, 305, 99, 533, 571, 249, 609, 247, 346, 522, 396, 674, 525, 556, 879, 354, 745, 163, 908, 520] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 6 4 1 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=120)
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
    · exact At81.checked
    · exact At82.checked
    · exact At83.checked
    · exact At84.checked
    · exact At85.checked
    · exact At86.checked
    · exact At87.checked
    · exact At88.checked
    · exact At89.checked
    · exact At90.checked
    · exact At91.checked
    · exact At92.checked
    · exact At93.checked
    · exact At94.checked
    · exact At95.checked
    · exact At96.checked
    · exact At97.checked
    · exact At98.checked
    · exact At99.checked
    · exact At100.checked
    · exact At101.checked
    · exact At102.checked
    · exact At103.checked
    · exact At104.checked
    · exact At105.checked
    · exact At106.checked
    · exact At107.checked
    · exact At108.checked
    · exact At109.checked
    · exact At110.checked
    · exact At111.checked
    · exact At112.checked
    · exact At113.checked
    · exact At114.checked
    · exact At115.checked
    · exact At116.checked
    · exact At117.checked
    · exact At118.checked
    · exact At119.checked
    · exact At120.checked
  · decide +kernel

end RKCert.FixedPolynomial.FixedReplay.N6K4J1W0
