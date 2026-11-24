module
public import RKCert.Dirk15Replay.G6K2J2W0Part000
public import RKCert.Dirk15Replay.G6K2J2W0Part001
public import RKCert.Dirk15Replay.G6K2J2W0Part002
public import RKCert.Dirk15Replay.G6K2J2W0Part003
public import RKCert.Dirk15Replay.G6K2J2W0Part004
public import RKCert.Dirk15Replay.G6K2J2W0Part005
public import RKCert.Dirk15Replay.G6K2J2W0Part006
public import RKCert.Dirk15Replay.G6K2J2W0Part007
public import RKCert.Dirk15Replay.G6K2J2W0Part008
public import RKCert.Dirk15Replay.G6K2J2W0Part009
public import RKCert.Dirk15Replay.G6K2J2W0Part010

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.G6K2J2W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [506, 509, 768, 81, 976, 149, 42, 776, 929, 690, 943, 357, 110, 600, 897, 1002, 951, 893, 230, 413, 209, 537, 180, 55, 112, 168, 1000, 297, 502, 68, 5, 205, 842, 59, 161, 414, 348, 367, 910, 347, 425, 746, 823, 102, 552, 220, 395, 964, 636, 517, 458, 760, 950, 256, 811, 711, 969, 867, 683, 855, 610, 939, 998, 284, 752, 746, 319, 238, 569, 645, 891, 451, 104, 151, 692, 798, 422, 421, 322, 154, 732, 292, 59, 617, 670, 390, 349, 267, 583, 554, 649, 718, 176, 387, 590, 156, 605, 934, 887, 844, 605, 382, 112, 764, 857, 425, 52, 767, 926, 322, 282, 7, 111, 336, 259, 365, 780, 704, 921, 628, 893]
private def values : Fin 121 → Nat := fun i => (#[506, 213, 585, 98, 244, 170, 482, 978, 480, 503, 1006, 195, 619, 748, 980, 855, 199, 426, 644, 281, 175, 250, 132, 910, 368, 129, 488, 499, 951, 470, 549, 811, 325, 255, 632, 389, 862, 318, 636, 7, 373, 287, 876, 944, 535, 224, 676, 400, 350, 970, 78, 810, 453, 935, 107, 1008, 82, 228, 485, 296, 436, 546, 860, 236, 808, 43, 2, 548, 188, 346, 1002, 778, 659, 780, 75, 145, 515, 62, 65, 877, 182, 693, 66, 307, 303, 775, 331, 655, 316, 470, 850, 249, 596, 376, 865, 200, 1006, 488, 522, 259, 408, 191, 768, 635, 248, 230, 592, 543, 851, 46, 472, 977, 902, 125, 484, 337, 41, 568, 953, 812, 441] : Array Nat)[i.val]!

theorem exactReduction : (nodeGramNorm 6 2 2 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=120)
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

end RKCert.FixedPolynomial.FixedReplay.G6K2J2W0
