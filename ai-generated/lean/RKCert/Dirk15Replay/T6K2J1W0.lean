module
public import RKCert.Dirk15Replay.T6K2J1W0Part000
public import RKCert.Dirk15Replay.T6K2J1W0Part001
public import RKCert.Dirk15Replay.T6K2J1W0Part002
public import RKCert.Dirk15Replay.T6K2J1W0Part003
public import RKCert.Dirk15Replay.T6K2J1W0Part004
public import RKCert.Dirk15Replay.T6K2J1W0Part005

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.T6K2J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [272, 260, 900, 981, 804, 274, 820, 772, 108, 797, 769, 998, 828, 198, 170, 233, 588, 552, 197, 811, 875, 730, 675, 401, 203, 621, 308, 89, 764, 798, 882, 103, 529, 81, 959, 183, 657, 272, 331, 749, 643, 595, 562, 141, 425, 105, 408, 692, 987, 903, 82, 867, 895, 514, 58, 612, 241, 830, 516, 743, 321, 528, 764, 491, 969, 379, 346, 43, 535, 383, 755, 393, 284, 843, 332, 723, 43, 778, 73, 586, 356, 983, 636, 43, 312, 334, 584, 528, 613, 727, 195, 247, 592, 874, 290, 950, 978, 550, 505, 258, 34, 1005, 947, 221, 743, 308, 489, 815, 744, 70, 868, 630, 247, 927, 340, 575, 580, 472, 870, 830, 142]
private def values : Fin 121 → Nat := fun i => (#[272, 775, 839, 582, 795, 371, 92, 926, 724, 225, 877, 636, 460, 802, 640, 160, 817, 214, 442, 187, 776, 706, 99, 583, 326, 648, 729, 596, 7, 568, 813, 202, 682, 169, 751, 669, 1, 520, 377, 59, 980, 389, 118, 544, 390, 143, 220, 252, 439, 610, 699, 909, 145, 611, 464, 247, 283, 408, 57, 816, 845, 460, 838, 761, 809, 430, 436, 48, 489, 393, 355, 436, 759, 412, 368, 710, 365, 861, 568, 286, 126, 15, 641, 136, 951, 771, 572, 1000, 313, 475, 917, 646, 105, 122, 29, 522, 1004, 256, 155, 354, 887, 9, 892, 508, 1006, 66, 310, 288, 322, 124, 838, 485, 581, 433, 796, 690, 197, 226, 467, 175, 176] : Array Nat)[i.val]!

theorem exactReduction : (parameterGramNorm 6 2 1 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=120)
    (by decide) ((parameterGramNorm_degree 6 2 1 0).trans (by decide)) (by decide) values
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

end RKCert.FixedPolynomial.FixedReplay.T6K2J1W0
