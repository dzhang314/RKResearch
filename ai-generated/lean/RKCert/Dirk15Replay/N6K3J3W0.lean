module
public import RKCert.Dirk15Replay.N6K3J3W0Part000
public import RKCert.Dirk15Replay.N6K3J3W0Part001
public import RKCert.Dirk15Replay.N6K3J3W0Part002
public import RKCert.Dirk15Replay.N6K3J3W0Part003
public import RKCert.Dirk15Replay.N6K3J3W0Part004
public import RKCert.Dirk15Replay.N6K3J3W0Part005

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N6K3J3W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [803, 503, 126, 53, 414, 388, 278, 990, 116, 256, 428, 245, 335, 884, 818, 749, 357, 349, 582, 394, 931, 225, 126, 790, 109, 966, 858, 210, 594, 162, 83, 595, 510, 509, 615, 193, 188, 939, 865, 66, 301, 490, 934, 818, 438, 274, 707, 421, 3, 213, 1, 684, 223, 267, 216, 956, 877, 408, 383, 521, 616, 902, 509, 781, 576, 538, 112, 782, 250, 766, 940, 391, 934, 1002, 1001, 336, 31, 11, 945, 92, 796, 863, 613, 793, 517, 720, 716, 944, 523, 479, 900, 188, 843, 323, 350, 603, 377, 611, 367, 205, 366, 438, 335, 282, 620, 325, 448, 360, 818, 840, 847, 841, 860, 243, 857, 549, 425, 226, 61, 647, 968]
private def values : Fin 121 → Nat := fun i => (#[803, 790, 40, 864, 917, 370, 329, 927, 935, 740, 983, 83, 89, 629, 745, 205, 674, 938, 365, 583, 561, 721, 715, 947, 92, 682, 407, 964, 322, 232, 621, 527, 430, 728, 308, 891, 200, 70, 215, 808, 20, 507, 381, 542, 133, 15, 997, 50, 748, 250, 0, 278, 850, 722, 744, 114, 230, 203, 542, 198, 400, 46, 38, 849, 796, 375, 337, 445, 546, 899, 491, 343, 50, 765, 583, 999, 56, 551, 265, 1002, 269, 547, 964, 712, 931, 915, 218, 710, 797, 97, 457, 12, 265, 996, 584, 336, 20, 822, 301, 522, 713, 401, 649, 896, 70, 962, 350, 874, 655, 169, 771, 528, 852, 337, 778, 318, 619, 668, 67, 333, 391] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 6 3 3 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=120)
    (by decide) ((nodeMomentNorm_degree (by decide) (by decide) 3 0).trans (by decide)) (by decide) values
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

end RKCert.FixedPolynomial.FixedReplay.N6K3J3W0
