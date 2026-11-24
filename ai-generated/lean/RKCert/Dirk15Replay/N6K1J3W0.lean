module
public import RKCert.Dirk15Replay.Axes

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N6K1J3W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000
noncomputable section

namespace At0
private def m : Array Nat := #[616993148949757952, 156500087051125636, 770115536281276416, 34902898055839744, 369296135812022272, 387173228512018432]
private def l : Array Nat := #[1, 1024, 1048576, 1073741824, 1099511627776, 1125899906842624]
private def u : Array Nat := #[156500087051125636, 770115536281276416, 34902898055839744, 369296135812022272, 387173228512018432, 616993148949757952]
private def swaps : List (Fin 6×Fin 6) := [(4, 5), (3, 4), (2, 3), (1, 2), (0, 1)]
private theorem evaluated : (rowMatrix 1009 6 m).det=(953:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 953 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[977, 640, 645, 963, 327, 142, 334]
theorem checked : (nodeMomentNorm 6 1 3 0).eval₂ order15Reduce (0:ZMod 1009)=(953:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 3 0 (by decide) 0 m coefficients 953
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At0

namespace At1
private def m : Array Nat := #[154248287237439777, 1052716412898150276, 385057768444137472, 731835250702811136, 277290102311354368, 952374981747015680]
private def l : Array Nat := #[1, 1275, 1305600, 1336934400, 1369020825600, 1401877325414400]
private def u : Array Nat := #[154248287237439777, 961518520443896832, 1018939415995613184, 585468261869551616, 1009124075391418368, 1076360310941548544]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(85:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 85 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[1001, 240, 827, 728, 1002, 881, 334]
theorem checked : (nodeMomentNorm 6 1 3 0).eval₂ order15Reduce (1:ZMod 1009)=(85:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 3 0 (by decide) 1 m coefficients 85
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At1

namespace At2
private def m : Array Nat := #[64176294690030146, 16888498603232132, 1113515008474353664, 22518619703345152, 758367121393582080, 943367782492274688]
private def l : Array Nat := #[1, 1654, 1693696, 1734344704, 1775968976896, 1818592232341504]
private def u : Array Nat := #[64176294690030146, 483011060036077568, 137359789240877056, 960393241159532544, 80574411106680832, 566327653141839872]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(591:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 591 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[306, 824, 583, 426, 108, 876, 442]
theorem checked : (nodeMomentNorm 6 1 3 0).eval₂ order15Reduce (2:ZMod 1009)=(591:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 3 0 (by decide) 2 m coefficients 591
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At2

namespace At3
private def m : Array Nat := #[77687093572141923, 291608075873128324, 605734150791368704, 1096627441142595584, 1005256959852544000, 37018357483962368]
private def l : Array Nat := #[1, 1444, 1478656, 1514143744, 1550483193856, 1587694790508544]
private def u : Array Nat := #[77687093572141923, 607985949695904768, 859061629830037504, 413206196745404416, 136061265402396672, 92323792361095168]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(731:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 731 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[158, 169, 764, 768, 434, 31, 187]
theorem checked : (nodeMomentNorm 6 1 3 0).eval₂ order15Reduce (3:ZMod 1009)=(731:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 3 0 (by decide) 3 m coefficients 731
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At3

namespace At4
private def m : Array Nat := #[114841790497947795, 575334852396732292, 1033576114636591104, 609112008385626112, 382968562903416832, 228421341647208448]
private def l : Array Nat := #[1, 1339, 1371136, 1404043264, 1437740302336, 1472246069592064]
private def u : Array Nat := #[114841790497947795, 753227037677865984, 61924495030484992, 415457223464976384, 157787615167250432, 560698153607626752]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(223:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 223 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[760, 88, 786, 727, 179, 556, 351]
theorem checked : (nodeMomentNorm 6 1 3 0).eval₂ order15Reduce (4:ZMod 1009)=(223:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 3 0 (by decide) 4 m coefficients 223
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At4

namespace At5
private def m : Array Nat := #[371546969258066356, 1027946614947763076, 1101130109350187008, 105835060338360320, 807750586643513344, 575198512954736640]
private def l : Array Nat := #[1, 1276, 1306624, 1337982976, 1370094567424, 1402976837042176]
private def u : Array Nat := #[371546969258066356, 552816854260174848, 387309568411041792, 202662451383107584, 858415116083789824, 220676381741154304]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(112:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 112 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[975, 175, 46, 186, 238, 330, 363]
theorem checked : (nodeMomentNorm 6 1 3 0).eval₂ order15Reduce (5:ZMod 1009)=(112:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 3 0 (by decide) 5 m coefficients 112
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At5

namespace At6
private def m : Array Nat := #[853432129386709717, 345651271401428868, 1131529407137976320, 933371802179076096, 445528575500615680, 500889119103123456]
private def l : Array Nat := #[1, 1234, 1263616, 1293942784, 1324997410816, 1356797348675584]
private def u : Array Nat := #[853432129386709717, 618119048857342976, 834291831730601984, 681170222102609920, 540103201307754496, 848928529759338496]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(446:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 446 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[405, 586, 722, 202, 846, 263, 444]
theorem checked : (nodeMomentNorm 6 1 3 0).eval₂ order15Reduce (6:ZMod 1009)=(446:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 3 0 (by decide) 6 m coefficients 446
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At6

namespace At7
private def m : Array Nat := #[356910270469111813, 945755921747810180, 781374535354945536, 809522039332274176, 335524636164882432, 914094384914366464]
private def l : Array Nat := #[1, 1204, 1232896, 1262485504, 1292785156096, 1323811999842304]
private def u : Array Nat := #[356910270469111813, 319755573543310336, 27021597769465856, 489766464845250560, 788135432347975680, 1053842312804696064]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(918:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 918 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[799, 739, 858, 886, 697, 432, 431]
theorem checked : (nodeMomentNorm 6 1 3 0).eval₂ order15Reduce (7:ZMod 1009)=(918:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 3 0 (by decide) 7 m coefficients 918
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At7

namespace At8
private def m : Array Nat := #[577586652210266406, 676665844012718980, 743093938825334784, 6755716064870400, 72381816824135680, 352270331399897088]
private def l : Array Nat := #[1, 1686, 1726464, 1767899136, 1810328715264, 1853776604430336]
private def u : Array Nat := #[577586652210266406, 21392098230310912, 213920982608379904, 395191182981857280, 879651083662655488, 1021191215506259968]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(447:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 447 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[736, 996, 941, 935, 556, 126, 325]
theorem checked : (nodeMomentNorm 6 1 3 0).eval₂ order15Reduce (8:ZMod 1009)=(447:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 3 0 (by decide) 8 m coefficients 447
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At8

namespace At9
private def m : Array Nat := #[577586652210266695, 589971551186132868, 483011060647727104, 108087017992093696, 713336622678016000, 399558127487287296]
private def l : Array Nat := #[1, 1164, 1191936, 1220542464, 1249835483136, 1279831534731264]
private def u : Array Nat := #[577586652210266695, 386183668047617024, 946881822265966592, 460493687890116608, 998188332741558272, 474003860780744704]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(67:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 67 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[736, 264, 763, 834, 265, 791, 545]
theorem checked : (nodeMomentNorm 6 1 3 0).eval₂ order15Reduce (9:ZMod 1009)=(67:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 3 0 (by decide) 9 m coefficients 67
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At9

namespace At10
private def m : Array Nat := #[924363823517795176, 373798769072644996, 1103381909621051392, 1015562653218635776, 163089327092400128, 547051015283671040]
private def l : Array Nat := #[1, 1150, 1177600, 1205862400, 1234803097600, 1264438371942400]
private def u : Array Nat := #[924363823517795176, 915356624263946240, 507780858900381696, 653022882271592448, 812732606972952576, 505529058172338176]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(859:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 859 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[637, 614, 694, 647, 242, 776, 879]
theorem checked : (nodeMomentNorm 6 1 3 0).eval₂ order15Reduce (10:ZMod 1009)=(859:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 3 0 (by decide) 10 m coefficients 859
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At10

namespace At11
private def m : Array Nat := #[460493061898633368, 759982437118927748, 832040031317004288, 755479001643876352, 331182664746795008, 152986047888752640]
private def l : Array Nat := #[1, 1322, 1353728, 1386217472, 1419486691328, 1453554371919872]
private def u : Array Nat := #[460493061898633368, 993043717835350016, 273593677522141184, 1018939578901331968, 8048425115320320, 75435293758455808]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(354:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 354 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[337, 756, 303, 469, 410, 42, 150]
theorem checked : (nodeMomentNorm 6 1 3 0).eval₂ order15Reduce (11:ZMod 1009)=(354:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 3 0 (by decide) 11 m coefficients 354
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At11

namespace At12
private def m : Array Nat := #[472877960873902521, 408701666184324996, 180143985558163456, 352407145305604096, 1082475661471252480, 167622746677706752]
private def l : Array Nat := #[1, 1129, 1156096, 1183842304, 1212254519296, 1241348627759104]
private def u : Array Nat := #[472877960873902521, 741968038609740800, 659777345872199680, 373799242591895552, 458726146712797184, 900719925474099200]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(1006:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 1006 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[874, 568, 381, 512, 592, 708, 633]
theorem checked : (nodeMomentNorm 6 1 3 0).eval₂ order15Reduce (12:ZMod 1009)=(1006:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 3 0 (by decide) 12 m coefficients 1006
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At12


def candidate : List Nat := [953, 1007, 397, 948, 475, 855, 42, 957, 608, 568, 492, 565, 290]
private def values : Fin 13 → Nat := fun i => (#[953, 85, 591, 731, 223, 112, 446, 918, 447, 67, 859, 354, 1006] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 6 1 3 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=12)
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
  · decide +kernel

end

end RKCert.FixedPolynomial.FixedReplay.N6K1J3W0
