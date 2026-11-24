module
public import RKCert.Dirk15Replay.N6K4J2W0Part000
public import RKCert.Dirk15Replay.N6K4J2W0Part001
public import RKCert.Dirk15Replay.N6K4J2W0Part002
public import RKCert.Dirk15Replay.N6K4J2W0Part003
public import RKCert.Dirk15Replay.N6K4J2W0Part004
public import RKCert.Dirk15Replay.N6K4J2W0Part005

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N6K4J2W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [997, 164, 625, 70, 833, 751, 492, 799, 521, 309, 642, 525, 961, 728, 800, 993, 327, 95, 155, 534, 387, 701, 53, 236, 377, 824, 661, 284, 126, 601, 181, 879, 688, 249, 306, 800, 80, 407, 233, 696, 141, 344, 217, 57, 392, 503, 26, 769, 684, 865, 542, 902, 101, 527, 647, 696, 44, 237, 22, 1002, 752, 748, 605, 17, 717, 22, 663, 763, 458, 437, 912, 594, 119, 152, 173, 129, 367, 904, 576, 557, 978, 149, 77, 110, 784, 736, 218, 258, 589, 20, 44, 903, 742, 292, 107, 546, 848, 544, 555, 945, 301, 484, 819, 993, 971, 305, 654, 97, 346, 0, 57, 486, 908, 806, 179, 831, 496, 72, 581, 238, 105]
private def values : Fin 121 → Nat := fun i => (#[997, 134, 500, 658, 803, 450, 155, 317, 654, 991, 38, 278, 209, 284, 718, 286, 385, 576, 319, 9, 911, 39, 230, 658, 335, 281, 246, 918, 904, 291, 86, 271, 596, 782, 922, 153, 39, 113, 4, 786, 626, 576, 783, 175, 806, 490, 765, 570, 495, 555, 328, 717, 474, 383, 265, 859, 182, 185, 985, 433, 637, 692, 105, 571, 603, 810, 899, 709, 771, 639, 655, 506, 963, 359, 884, 246, 424, 935, 789, 111, 696, 186, 4, 270, 318, 820, 65, 109, 379, 986, 553, 855, 167, 304, 301, 730, 554, 838, 353, 528, 103, 138, 149, 121, 216, 903, 782, 175, 864, 755, 979, 652, 759, 689, 938, 647, 539, 819, 820, 686, 237] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 6 4 2 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=120)
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

end RKCert.FixedPolynomial.FixedReplay.N6K4J2W0
