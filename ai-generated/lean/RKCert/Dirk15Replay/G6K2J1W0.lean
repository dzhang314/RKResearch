module
public import RKCert.Dirk15Replay.G6K2J1W0Part000
public import RKCert.Dirk15Replay.G6K2J1W0Part001
public import RKCert.Dirk15Replay.G6K2J1W0Part002
public import RKCert.Dirk15Replay.G6K2J1W0Part003
public import RKCert.Dirk15Replay.G6K2J1W0Part004
public import RKCert.Dirk15Replay.G6K2J1W0Part005
public import RKCert.Dirk15Replay.G6K2J1W0Part006
public import RKCert.Dirk15Replay.G6K2J1W0Part007
public import RKCert.Dirk15Replay.G6K2J1W0Part008
public import RKCert.Dirk15Replay.G6K2J1W0Part009
public import RKCert.Dirk15Replay.G6K2J1W0Part010

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.G6K2J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [791, 139, 371, 744, 835, 887, 256, 982, 599, 899, 755, 350, 577, 314, 565, 4, 367, 332, 160, 267, 451, 908, 662, 467, 139, 922, 350, 31, 542, 629, 216, 958, 306, 993, 942, 576, 895, 211, 846, 8, 473, 249, 569, 400, 534, 558, 519, 326, 126, 943, 324, 591, 374, 292, 936, 300, 17, 512, 607, 812, 347, 880, 434, 134, 452, 910, 458, 659, 465, 738, 912, 692, 592, 424, 715, 947, 879, 542, 962, 862, 3, 165, 752, 808, 44, 393, 605, 611, 595, 904, 17, 954, 463, 309, 480, 820, 468, 648, 717, 392, 283, 940, 199, 65, 469, 905, 99, 79, 335, 834, 566, 32, 270, 376, 344, 205, 239, 900, 122, 80, 1008]
private def values : Fin 121 → Nat := fun i => (#[791, 661, 428, 111, 36, 326, 250, 453, 577, 417, 552, 102, 3, 523, 675, 3, 224, 996, 853, 172, 497, 764, 333, 760, 597, 286, 882, 630, 46, 928, 905, 1005, 227, 63, 796, 548, 945, 666, 25, 96, 31, 968, 994, 1002, 151, 779, 915, 131, 408, 751, 679, 305, 457, 416, 645, 626, 246, 593, 227, 383, 964, 749, 848, 896, 395, 289, 744, 988, 246, 435, 826, 985, 808, 207, 483, 708, 615, 474, 185, 15, 33, 747, 687, 388, 87, 821, 224, 867, 246, 194, 422, 102, 797, 698, 380, 499, 369, 577, 699, 590, 684, 728, 521, 277, 202, 8, 794, 353, 323, 466, 593, 120, 691, 811, 504, 888, 392, 707, 943, 827, 790] : Array Nat)[i.val]!

theorem exactReduction : (nodeGramNorm 6 2 1 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=120)
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

end RKCert.FixedPolynomial.FixedReplay.G6K2J1W0
