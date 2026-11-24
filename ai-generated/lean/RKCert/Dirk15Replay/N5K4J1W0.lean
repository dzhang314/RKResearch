module
public import RKCert.Dirk15Replay.Axes

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N5K4J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000
noncomputable section

namespace At0
private def m : Array Nat := #[142336, 145752064, 149250113536, 152832116260864, 1036463940845786]
private def l : Array Nat := #[1, 1024, 1048576, 1073741824, 1099511627776]
private def u : Array Nat := #[1036463940845786, 142336, 145752064, 149250113536, 152832116260864]
private def swaps : List (Fin 5×Fin 5) := [(3, 4), (2, 4), (1, 4), (0, 4)]
private theorem evaluated : (rowMatrix 1009 5 m).det=(251:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 251 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[320, 245, 793, 677, 332, 1001]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (0:ZMod 1009)=(251:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 0 m coefficients 251
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At0

namespace At1
private def m : Array Nat := #[366964574567833, 930054948117200, 610826932361325, 749220278127807, 812014756083930]
private def l : Array Nat := #[1, 1830, 1106426, 1893692399, 1424819283971]
private def u : Array Nat := #[366964574567833, 925566349696000, 975394986524672, 301051437645824, 575044581326848]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(608:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 608 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[341, 904, 700, 93, 292, 8]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (1:ZMod 1009)=(608:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 1 m coefficients 608
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At1

namespace At2
private def m : Array Nat := #[475332818061802, 813148991010507, 198212293735860, 961423527255422, 247469954067674]
private def l : Array Nat := #[1, 1427, 1561207, 1741821180, 1109233999668]
private def u : Array Nat := #[475332818061802, 210823742109696, 410710731390976, 350542345797632, 962072674304000]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(862:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 862 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[328, 860, 571, 612, 17, 161]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (2:ZMod 1009)=(862:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 2 m coefficients 862
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At2

namespace At3
private def m : Array Nat := #[373524785642313, 122526606309645, 315991508764629, 397509003724349, 67452883201242]
private def l : Array Nat := #[1, 1629, 1308489, 1370602907, 1724460962091]
private def u : Array Nat := #[373524785642313, 936930181706752, 106466157527040, 685403765997568, 1039038488248320]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(875:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 875 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[969, 294, 670, 162, 541, 518]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (3:ZMod 1009)=(875:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 3 m coefficients 875
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At3

namespace At4
private def m : Array Nat := #[902581932992265, 1105289835408035, 742121575335647, 554575747413756, 904610696261850]
private def l : Array Nat := #[1, 1730, 1516954, 1557251608, 1809170041640]
private def u : Array Nat := #[902581932992265, 266874181072896, 954108621094912, 750608885743616, 323256418566144]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(255:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 255 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[928, 39, 584, 470, 607, 525]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (4:ZMod 1009)=(255:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 4 m coefficients 255
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At4

namespace At5
private def m : Array Nat := #[465429765120348, 716662187691207, 252933904729795, 1033714301809595, 880629243481306]
private def l : Array Nat := #[1, 1387, 1463962, 1458174178, 1399219856518]
private def u : Array Nat := #[465429765120348, 516994505156608, 412252998991872, 375860104265728, 868614185943040]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(420:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 420 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[930, 600, 58, 434, 729, 611]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (5:ZMod 1009)=(420:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 5 m coefficients 420
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At5

namespace At6
private def m : Array Nat := #[1094202030808403, 96340013635718, 349378100106113, 191086791385225, 502670603945178]
private def l : Array Nat := #[1, 1831, 1235911, 1888569002, 1417435795790]
private def u : Array Nat := #[1094202030808403, 315179996385280, 159646772887552, 16685947944960, 649811372015616]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(304:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 304 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[783, 165, 839, 594, 191, 765]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (6:ZMod 1009)=(304:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 6 m coefficients 304
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At6

namespace At7
private def m : Array Nat := #[148376214666492, 1004831179004668, 813134121051432, 222678562927944, 198766725486810]
private def l : Array Nat := #[1, 2004, 1662786, 1084825282, 1698449044617]
private def u : Array Nat := #[148376214666492, 839772885456896, 14919038664704, 499529392586752, 599233837137920]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(777:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 777 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[436, 688, 448, 540, 100, 122]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (7:ZMod 1009)=(777:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 7 m coefficients 777
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At7

namespace At8
private def m : Array Nat := #[945313238252868, 649946158478691, 446687000678298, 55600642280967, 337856554561754]
private def l : Array Nat := #[1, 1377, 1243743, 2097929283, 1481150310955]
private def u : Array Nat := #[945313238252868, 71440786230272, 653224117796864, 327482666385408, 269380348805120]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(857:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 857 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[28, 855, 78, 356, 385, 585]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (8:ZMod 1009)=(857:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 8 m coefficients 857
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At8

namespace At9
private def m : Array Nat := #[568665462813190, 815694421012680, 742758608849653, 431728944881350, 951018847673562]
private def l : Array Nat := #[1, 1562, 1749646, 1752173344, 2062446929099]
private def u : Array Nat := #[568665462813190, 77156117852160, 127121139695616, 663200932560896, 489282674360320]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(398:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 398 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[946, 149, 384, 46, 832, 357]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (9:ZMod 1009)=(398:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 9 m coefficients 398
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At9

namespace At10
private def m : Array Nat := #[1105241662401035, 555446582067783, 295901306091306, 122787894596485, 540211042872538]
private def l : Array Nat := #[1, 1710, 1942175, 1687783185, 2042744947327]
private def u : Array Nat := #[1105241662401035, 244441681221632, 77770232168448, 716451010838528, 302365697638400]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(914:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 914 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[829, 897, 300, 978, 101, 590]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (10:ZMod 1009)=(914:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 10 m coefficients 914
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At10

namespace At11
private def m : Array Nat := #[1104199963043579, 581342647242507, 1039304366208072, 1018701585481811, 615866535988442]
private def l : Array Nat := #[1, 1189, 1692386, 1561018462, 2141907031761]
private def u : Array Nat := #[1104199963043579, 378867289016320, 543061900787712, 223831146889216, 273778395316224]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(304:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 304 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[680, 227, 901, 265, 797, 935]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (11:ZMod 1009)=(304:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 11 m coefficients 304
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At11

namespace At12
private def m : Array Nat := #[979713407191419, 800132467041343, 774199822835249, 1013535102959890, 243391700436186]
private def l : Array Nat := #[1, 1932, 1998318, 1972111178, 2077493830803]
private def u : Array Nat := #[979713407191419, 1008502510642176, 1101749709438976, 486140905783296, 91259465105408]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(445:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 445 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[879, 187, 184, 281, 415, 137]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (12:ZMod 1009)=(445:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 12 m coefficients 445
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At12

namespace At13
private def m : Array Nat := #[982849410315520, 268566957358817, 854878151469315, 200265335508433, 841031039158490]
private def l : Array Nat := #[1, 1086, 1238825, 1154960508, 1583477243409]
private def u : Array Nat := #[982849410315520, 411111522526208, 430646174416896, 1066483329269760, 266081813921792]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(604:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 604 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[223, 711, 966, 15, 447, 666]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (13:ZMod 1009)=(604:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 13 m coefficients 604
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At13

namespace At14
private def m : Array Nat := #[701642853935085, 1007372500441146, 168473632040111, 418040024818320, 173895650577626]
private def l : Array Nat := #[1, 1514, 1618633, 1697015629, 1158007224770]
private def u : Array Nat := #[701642853935085, 85483223260160, 982064210903040, 169610406002688, 152832116260864]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(956:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 956 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[11, 657, 620, 551, 354, 231]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (14:ZMod 1009)=(956:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 14 m coefficients 956
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At14

namespace At15
private def m : Array Nat := #[588133170645937, 506382396078408, 942129720047925, 350507133851471, 279382495578330]
private def l : Array Nat := #[1, 1145, 1224778, 1449541588, 2152429670287]
private def u : Array Nat := #[588133170645937, 464680682903552, 830248171077632, 1007559599194112, 924689278959616]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(156:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 156 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[57, 863, 991, 458, 619, 447]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (15:ZMod 1009)=(156:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 15 m coefficients 156
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At15

namespace At16
private def m : Array Nat := #[781585520698507, 1013796734214966, 840601828720277, 614795436582941, 446914016753882]
private def l : Array Nat := #[1, 1705, 1923476, 1969646207, 2016917844318]
private def u : Array Nat := #[781585520698507, 795171783877632, 600433652400128, 878320812032, 899400511520768]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(804:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 804 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[757, 140, 150, 261, 755, 367]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (16:ZMod 1009)=(804:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 16 m coefficients 804
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At16

namespace At17
private def m : Array Nat := #[731103205516682, 468474391396143, 224887438515422, 1089716171296988, 940283363814618]
private def l : Array Nat := #[1, 1843, 1695847, 1093104518, 1740513786548]
private def u : Array Nat := #[731103205516682, 506978979050496, 740861415522304, 1011997374152704, 56075093016576]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(330:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 330 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[111, 346, 292, 858, 340, 104]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (17:ZMod 1009)=(330:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 17 m coefficients 330
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At17

namespace At18
private def m : Array Nat := #[92770267345112, 918923115285071, 137828421016577, 451310009952667, 518294879196378]
private def l : Array Nat := #[1, 1293, 1565340, 1200057444, 2167752570184]
private def u : Array Nat := #[92770267345112, 481200452737024, 254123939201024, 982754015576064, 742170348748800]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(496:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 496 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[835, 361, 499, 928, 52, 417]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (18:ZMod 1009)=(496:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 18 m coefficients 496
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At18

namespace At19
private def m : Array Nat := #[712452566379360, 405961655006642, 1023033354864623, 153794005598810, 807882347241690]
private def l : Array Nat := #[1, 1863, 2059939, 1952751235, 1390515256402]
private def u : Array Nat := #[712452566379360, 416552281763840, 371433920266240, 472279972577280, 609129441787904]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(899:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 899 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[320, 152, 602, 393, 686, 279]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (19:ZMod 1009)=(899:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 19 m coefficients 899
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At19

namespace At20
private def m : Array Nat := #[964916369344808, 841828441163380, 1053620143678677, 642982013400857, 84777695832282]
private def l : Array Nat := #[1, 1367, 1866148, 2050147285, 1875580131431]
private def u : Array Nat := #[964916369344808, 700030079538176, 992405698379776, 784739917103104, 998356558020608]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(262:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 262 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[771, 802, 1007, 853, 153, 499]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (20:ZMod 1009)=(262:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 20 m coefficients 262
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At20

namespace At21
private def m : Array Nat := #[778122387469544, 46856277022144, 736968963484294, 898634163951576, 1091378959457498]
private def l : Array Nat := #[1, 1687, 1549741, 1854743765, 1594992109769]
private def u : Array Nat := #[778122387469544, 534867199255552, 590875607433216, 574556028796928, 463993906921472]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(1006:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 1006 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[175, 503, 503, 976, 569, 281]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (21:ZMod 1009)=(1006:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 21 m coefficients 1006
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At21

namespace At22
private def m : Array Nat := #[495566102976612, 501417498337458, 473941642136864, 194784292596902, 241029743669466]
private def l : Array Nat := #[1, 1611, 1197745, 1841244424, 2140997623775]
private def u : Array Nat := #[495566102976612, 730907028662272, 801151745261568, 753278207918080, 505775348776960]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(641:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 641 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[422, 639, 124, 969, 209, 846]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (22:ZMod 1009)=(641:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 22 m coefficients 641
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At22

namespace At23
private def m : Array Nat := #[463810027814975, 758682130383974, 1065897078645908, 968014635900261, 856661441556698]
private def l : Array Nat := #[1, 1410, 1340051, 1305388374, 1407904344612]
private def u : Array Nat := #[463810027814975, 696076094266368, 918892756074496, 314253093371904, 984062906859520]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(483:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 483 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[291, 770, 957, 995, 596, 982]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (23:ZMod 1009)=(483:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 23 m coefficients 483
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At23

namespace At24
private def m : Array Nat := #[811081376540682, 940481361299960, 503301978943714, 593106045268516, 150337480043738]
private def l : Array Nat := #[1, 1478, 1343092, 1392975710, 2074307983165]
private def u : Array Nat := #[811081376540682, 260462167813120, 685500661760000, 868593784848384, 23089744183296]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(404:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 404 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[544, 679, 941, 599, 473, 666]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (24:ZMod 1009)=(404:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 24 m coefficients 404
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At24

namespace At25
private def m : Array Nat := #[177607355455029, 491323398442643, 358576909834762, 911125435800291, 345576262839514]
private def l : Array Nat := #[1, 1702, 1945667, 1710889656, 1631389573724]
private def u : Array Nat := #[177607355455029, 286582659093504, 1003765964472320, 727971186868224, 1044536046387200]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(311:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 311 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[948, 401, 747, 152, 874, 650]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (25:ZMod 1009)=(311:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 25 m coefficients 311
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At25

namespace At26
private def m : Array Nat := #[293711906382908, 744233189417811, 702282526768155, 3018232675234, 223523876417754]
private def l : Array Nat := #[1, 1055, 1160127, 1168064008, 1304353816531]
private def u : Array Nat := #[293711906382908, 518773576747008, 498356718665728, 348880193454080, 338649581355008]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(873:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 873 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[324, 252, 577, 277, 105, 29]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (26:ZMod 1009)=(873:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 26 m coefficients 873
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At26

namespace At27
private def m : Array Nat := #[398604337619533, 454900146174307, 169658769671927, 607096534439024, 586992040339674]
private def l : Array Nat := #[1, 1876, 1523097, 1778712643, 1197195065045]
private def u : Array Nat := #[398604337619533, 817933010933760, 527359983747072, 947757548306432, 741070837121024]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(462:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 462 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[632, 858, 999, 266, 833, 872]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (27:ZMod 1009)=(462:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 27 m coefficients 462
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At27

namespace At28
private def m : Array Nat := #[251740228409265, 187098808838608, 97367332570812, 787983032897839, 662199555015898]
private def l : Array Nat := #[1, 1269, 1900455, 1155122660, 1827255138191]
private def u : Array Nat := #[251740228409265, 895492597886976, 453873292541952, 764691009765376, 315559837171712]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(1003:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 1003 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[966, 157, 755, 533, 22, 745]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (28:ZMod 1009)=(1003:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 28 m coefficients 1003
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At28

namespace At29
private def m : Array Nat := #[937763306448528, 380904658544069, 493366743961435, 128169403992558, 733869780371674]
private def l : Array Nat := #[1, 2026, 2014217, 1545507755, 1372209981548]
private def u : Array Nat := #[937763306448528, 282302916040704, 654233653215232, 1096084243873792, 85761906966528]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(328:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 328 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[630, 491, 623, 22, 58, 369]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (29:ZMod 1009)=(328:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 29 m coefficients 328
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At29

namespace At30
private def m : Array Nat := #[795987500614626, 105988750436958, 69412732633315, 384844775304877, 725627734458586]
private def l : Array Nat := #[1, 1589, 1742347, 1643052659, 2083238407288]
private def u : Array Nat := #[795987500614626, 271346763778048, 277509798100992, 992173952598016, 788349837115392]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(386:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 386 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[196, 563, 216, 678, 703, 179]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (30:ZMod 1009)=(386:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 30 m coefficients 386
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At30

namespace At31
private def m : Array Nat := #[834409969659819, 200093010202822, 326421737558838, 592649083740012, 460772418010330]
private def l : Array Nat := #[1, 1050, 1893912, 1361224590, 1205412762938]
private def u : Array Nat := #[834409969659819, 718521119769600, 788294863421440, 830069001945088, 575044581326848]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(179:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 179 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[544, 511, 835, 819, 130, 919]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (31:ZMod 1009)=(179:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 31 m coefficients 179
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At31

namespace At32
private def m : Array Nat := #[1097228754106574, 35819691850250, 368979902934642, 1041163548148794, 494893123070170]
private def l : Array Nat := #[1, 1869, 1320037, 1339799758, 1366316003476]
private def u : Array Nat := #[1097228754106574, 90359503163392, 1106555421327360, 209114441449472, 1092914558009344]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(704:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 704 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[893, 928, 250, 616, 1003, 201]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (32:ZMod 1009)=(704:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 32 m coefficients 704
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At32

namespace At33
private def m : Array Nat := #[887761246598398, 496471530928981, 226606138842760, 595751062996217, 511510136728794]
private def l : Array Nat := #[1, 1079, 1549394, 1778633567, 1620859053613]
private def u : Array Nat := #[887761246598398, 508444867142656, 796446268850176, 346770290769920, 924689278959616]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(480:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 480 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[868, 873, 598, 510, 413, 163]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (33:ZMod 1009)=(480:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 33 m coefficients 480
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At33

namespace At34
private def m : Array Nat := #[612466451319034, 182039966675410, 450104278990712, 682280026183096, 910615115513050]
private def l : Array Nat := #[1, 1938, 1814806, 1337074029, 1402332800800]
private def u : Array Nat := #[612466451319034, 673840811309056, 274951661682688, 491505319936000, 368336395304960]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(964:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 964 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[549, 927, 137, 638, 1003, 1001]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (34:ZMod 1009)=(964:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 34 m coefficients 964
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At34

namespace At35
private def m : Array Nat := #[51985810830432, 751036754926222, 214840021656913, 388048965631607, 80921452353754]
private def l : Array Nat := #[1, 1220, 1354730, 1747649454, 1747677571810]
private def u : Array Nat := #[51985810830432, 607271195486208, 545092023615488, 413495828938752, 562949953421312]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(546:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 546 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[520, 195, 135, 259, 904, 555]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (35:ZMod 1009)=(546:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 35 m coefficients 546
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At35

namespace At36
private def m : Array Nat := #[463070165772717, 669671040946868, 591702628494340, 437967894614838, 545120719382746]
private def l : Array Nat := #[1, 1663, 1872039, 1641464325, 1717615267341]
private def u : Array Nat := #[463070165772717, 1092720152247296, 668768648822784, 594689761738752, 847723465015296]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(123:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 123 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[909, 371, 660, 207, 824, 958]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (36:ZMod 1009)=(123:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 36 m coefficients 123
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At36

namespace At37
private def m : Array Nat := #[548285612714587, 1016083962242912, 773617249540994, 524020153154564, 658707253170394]
private def l : Array Nat := #[1, 1673, 1999651, 1420066463, 1822520413934]
private def u : Array Nat := #[548285612714587, 661935394717696, 773173120335872, 156459216142336, 36283883716608]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(389:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 389 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[428, 722, 406, 299, 38, 150]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (37:ZMod 1009)=(389:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 37 m coefficients 389
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At37

namespace At38
private def m : Array Nat := #[1101510238679747, 409651249580477, 570482504936425, 1058790477347011, 162244557118682]
private def l : Array Nat := #[1, 1948, 2059685, 2024449735, 1972739437432]
private def u : Array Nat := #[1101510238679747, 770860404066304, 151393256079360, 502729143222272, 229797930205184]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(925:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 925 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[458, 135, 555, 779, 450, 545]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (38:ZMod 1009)=(925:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 38 m coefficients 925
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At38

namespace At39
private def m : Array Nat := #[266754721670700, 489943191945944, 305955925330233, 501100418334082, 152415192393946]
private def l : Array Nat := #[1, 1381, 1524938, 1090876144, 2052569563728]
private def u : Array Nat := #[266754721670700, 907229092317184, 693473944535040, 622974268866560, 125344325566464]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(561:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 561 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[53, 173, 567, 735, 565, 545]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (39:ZMod 1009)=(561:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 39 m coefficients 561
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At39

namespace At40
private def m : Array Nat := #[532530808132284, 122563242517468, 329471914026836, 446294403049025, 736512821877978]
private def l : Array Nat := #[1, 1700, 2044009, 1241236981, 1510145352254]
private def u : Array Nat := #[532530808132284, 936802517140480, 192182063464448, 918897515560960, 190215511605248]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(403:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 403 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[25, 59, 24, 552, 560, 180]
theorem checked : (nodeMomentNorm 5 4 1 0).eval₂ order15Reduce (40:ZMod 1009)=(403:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 1 0 (by decide) 40 m coefficients 403
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At40


def candidate : List Nat := [251, 125, 758, 236, 833, 547, 625, 68, 670, 623, 528, 299, 222, 475, 190, 349, 439, 161, 177, 921, 68, 949, 401, 108, 112, 983, 952, 884, 442, 545, 671, 464, 740, 318, 22, 818, 24, 896, 856, 69, 960]
private def values : Fin 41 → Nat := fun i => (#[251, 608, 862, 875, 255, 420, 304, 777, 857, 398, 914, 304, 445, 604, 956, 156, 804, 330, 496, 899, 262, 1006, 641, 483, 404, 311, 873, 462, 1003, 328, 386, 179, 704, 480, 964, 546, 123, 389, 925, 561, 403] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 5 4 1 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=40)
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
  · decide +kernel

end

end RKCert.FixedPolynomial.FixedReplay.N5K4J1W0
