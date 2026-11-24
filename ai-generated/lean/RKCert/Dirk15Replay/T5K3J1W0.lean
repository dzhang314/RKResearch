module
public import RKCert.Dirk15Replay.T5K3J1W0Part000
public import RKCert.Dirk15Replay.T5K3J1W0Part001
public import RKCert.Dirk15Replay.T5K3J1W0Part002
public import RKCert.Dirk15Replay.T5K3J1W0Part003
public import RKCert.Dirk15Replay.T5K3J1W0Part004
public import RKCert.Dirk15Replay.T5K3J1W0Part005

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.T5K3J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [919, 347, 827, 698, 310, 954, 120, 756, 411, 303, 341, 595, 580, 854, 853, 71, 859, 221, 931, 612, 403, 368, 869, 771, 391, 283, 742, 419, 624, 608, 587, 942, 336, 226, 18, 364, 430, 341, 557, 822, 355, 830, 401, 630, 46, 150, 976, 834, 31, 50, 944, 872, 97, 196, 84, 989, 68, 777, 509, 459, 49, 26, 177, 716, 524, 823, 805, 856, 273, 196, 605, 467, 598, 941, 725, 349, 709, 729, 359, 351, 211, 54, 417, 771, 162, 622, 529, 764, 267, 835, 296, 852, 236, 830, 827, 212, 457, 961, 140, 645, 703, 551, 994, 401, 794, 493, 863, 374, 692, 115, 933, 363, 309, 567, 392, 13, 989, 583, 672, 247, 349]
private def values : Fin 121 → Nat := fun i => (#[919, 166, 39, 906, 184, 689, 323, 184, 553, 373, 1005, 378, 128, 278, 283, 582, 562, 471, 186, 691, 381, 771, 134, 986, 997, 11, 616, 855, 114, 576, 328, 882, 668, 821, 182, 231, 291, 274, 125, 567, 336, 152, 964, 213, 221, 433, 411, 650, 650, 793, 514, 83, 357, 496, 645, 71, 168, 789, 198, 676, 688, 378, 74, 467, 962, 111, 366, 451, 198, 952, 490, 155, 62, 933, 6, 670, 894, 499, 709, 94, 754, 963, 540, 820, 242, 555, 135, 101, 18, 542, 496, 800, 409, 948, 545, 791, 27, 622, 708, 514, 270, 309, 152, 832, 549, 784, 526, 66, 828, 451, 858, 39, 262, 119, 276, 245, 288, 213, 121, 334, 797] : Array Nat)[i.val]!

theorem exactReduction : (parameterGramNorm 5 3 1 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=120)
    (by decide) ((parameterGramNorm_degree 5 3 1 0).trans (by decide)) (by decide) values
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

end RKCert.FixedPolynomial.FixedReplay.T5K3J1W0
