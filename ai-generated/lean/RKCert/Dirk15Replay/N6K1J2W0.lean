module
public import RKCert.Dirk15Replay.Axes

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N6K1J2W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000
noncomputable section

namespace At0
private def m : Array Nat := #[65302194596872192, 966022120070971583, 1026820715040668672, 803892533685911552, 113716095675793408, 136443895448862720]
private def l : Array Nat := #[1, 1024, 1048576, 1073741824, 1099511627776, 1125899906842624]
private def u : Array Nat := #[966022120070971583, 1026820715040668672, 803892533685911552, 113716095675793408, 136443895448862720, 65302194596872192]
private def swaps : List (Fin 6×Fin 6) := [(4, 5), (3, 4), (2, 3), (1, 2), (0, 1)]
private theorem evaluated : (rowMatrix 1009 6 m).det=(12:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 12 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[977, 640, 645, 963, 327, 142, 334]
theorem checked : (nodeMomentNorm 6 1 2 0).eval₂ order15Reduce (0:ZMod 1009)=(12:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 0 (by decide) 0 m coefficients 12
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At0

namespace At1
private def m : Array Nat := #[584342051651321965, 646266546527777983, 513410357634726912, 218424699165605888, 369415221296496640, 353742577469489152]
private def l : Array Nat := #[1, 1359, 1391616, 1425014784, 1459215138816, 1494236302147584]
private def u : Array Nat := #[584342051651321965, 289356276058665984, 141863388376465408, 407575883314888704, 155494033911709696, 560698153607626752]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(855:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 855 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[1001, 240, 827, 728, 1002, 881, 334]
theorem checked : (nodeMomentNorm 6 1 2 0).eval₂ order15Reduce (1:ZMod 1009)=(855:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 0 (by decide) 1 m coefficients 855
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At1

namespace At2
private def m : Array Nat := #[85568392920039642, 22517998137075903, 727331340049120256, 408701900459868160, 631869746358255616, 764696043467046912]
private def l : Array Nat := #[1, 1696, 1736704, 1778384896, 1821066133504, 1864771720708096]
private def u : Array Nat := #[85568392920039642, 458241262085171200, 654147846104154112, 466122795508563968, 942617915562131456, 256705178760118272]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(941:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 941 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[306, 824, 583, 426, 108, 876, 442]
theorem checked : (nodeMomentNorm 6 1 2 0).eval₂ order15Reduce (2:ZMod 1009)=(941:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 0 (by decide) 2 m coefficients 941
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At2

namespace At3
private def m : Array Nat := #[103582791429521735, 10133099161918655, 428967864850119680, 704813692997337088, 960752365923729408, 835627737598132224]
private def l : Array Nat := #[1, 1472, 1507328, 1543503872, 1580547964928, 1618481116086272]
private def u : Array Nat := #[103582791429521735, 182395784908839936, 510032658142593024, 552817205373304832, 953996761397985280, 754352937584558080]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(869:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 869 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[158, 169, 764, 768, 434, 31, 187]
theorem checked : (nodeMomentNorm 6 1 2 0).eval₂ order15Reduce (3:ZMod 1009)=(869:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 0 (by decide) 3 m coefficients 869
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At3

namespace At4
private def m : Array Nat := #[153122387330597300, 388435467861151935, 242068480428538880, 433471932486123520, 132209881254985728, 479843367035863040]
private def l : Array Nat := #[1, 1360, 1392640, 1426063360, 1460288880640, 1495335813775360]
private def u : Array Nat := #[153122387330597300, 60798594969948160, 262334678751510528, 899594493718691840, 53396682691313664, 875950127523561472]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(877:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 877 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[760, 88, 786, 727, 179, 556, 351]
theorem checked : (nodeMomentNorm 6 1 2 0).eval₂ order15Reduce (4:ZMod 1009)=(877:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 0 (by decide) 4 m coefficients 877
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At4

namespace At5
private def m : Array Nat := #[495395959010755105, 991917817928910015, 332140473090243584, 898468711049986048, 1076959749863374848, 684757150081220608]
private def l : Array Nat := #[1, 1091, 1117184, 1143996416, 1171452329984, 1199567185903616]
private def u : Array Nat := #[495395959010755105, 745345738330375168, 379428269177438208, 469500846342668288, 293333209616220160, 383931868233334784]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(1004:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 1004 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[975, 175, 46, 186, 238, 330, 363]
theorem checked : (nodeMomentNorm 6 1 2 0).eval₂ order15Reduce (5:ZMod 1009)=(1004:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 0 (by decide) 5 m coefficients 1004
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At5

namespace At6
private def m : Array Nat := #[380554168512807566, 82190693200181439, 372672869850872832, 865817730789408768, 972370905294438400, 1335906627747840]
private def l : Array Nat := #[1, 1248, 1277952, 1308622848, 1340029796352, 1372190511464448]
private def u : Array Nat := #[380554168512807566, 40532396647004160, 381680069105418240, 571957854903205888, 89665173245132800, 525795256495505408]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(567:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 567 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[405, 586, 722, 202, 846, 263, 444]
theorem checked : (nodeMomentNorm 6 1 2 0).eval₂ order15Reduce (6:ZMod 1009)=(567:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 0 (by decide) 6 m coefficients 567
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At6

namespace At7
private def m : Array Nat := #[854558029293552379, 124974889660312767, 663155045930564608, 322008192822280192, 69519026774081536, 163465493213085696]
private def l : Array Nat := #[1, 1216, 1245184, 1275068416, 1305670057984, 1337006139375616]
private def u : Array Nat := #[854558029293552379, 774619135908506624, 756604738198306816, 466123380697858048, 320594500915298304, 115967690404790272]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(497:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 497 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[799, 739, 858, 886, 697, 432, 431]
theorem checked : (nodeMomentNorm 6 1 2 0).eval₂ order15Reduce (7:ZMod 1009)=(497:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 0 (by decide) 7 m coefficients 497
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At7

namespace At8
private def m : Array Nat := #[770115536280355688, 523543456682713279, 990791918936062976, 9008135757889536, 854391108610818048, 23853904764600320]
private def l : Array Nat := #[1, 1192, 1220608, 1249902592, 1279900254208, 1310617860308992]
private def u : Array Nat := #[770115536280355688, 651896046062772224, 531424756944076800, 476256596897300480, 365750343956430848, 84442493013196800]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(939:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 939 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[736, 996, 941, 935, 556, 126, 325]
theorem checked : (nodeMomentNorm 6 1 2 0).eval₂ order15Reduce (8:ZMod 1009)=(939:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 0 (by decide) 8 m coefficients 939
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At8

namespace At9
private def m : Array Nat := #[770115536280355797, 29273397578912959, 644014747742829568, 144116241616863232, 951338347366711296, 162339593306243072]
private def l : Array Nat := #[1, 1846, 1890304, 1935671296, 1982127407104, 2029698464874496]
private def u : Array Nat := #[770115536280355797, 900719925475103744, 945755922776457216, 915357677603782656, 582042972837642240, 879327827244089344]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(237:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 237 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[736, 264, 763, 834, 265, 791, 545]
theorem checked : (nodeMomentNorm 6 1 2 0).eval₂ order15Reduce (9:ZMod 1009)=(237:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 0 (by decide) 9 m coefficients 237
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At9

namespace At10
private def m : Array Nat := #[475129760687587409, 877076027430487231, 713820541023353856, 596727037799956480, 216262047640322048, 761318343746519040]
private def l : Array Nat := #[1, 1562, 1599488, 1637875712, 1677184729088, 1717437162586112]
private def u : Array Nat := #[475129760687587409, 864691128455218176, 147492887881318400, 767863823439757312, 621585809018978304, 389561367767547904]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(101:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 101 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[637, 614, 694, 647, 242, 776, 879]
theorem checked : (nodeMomentNorm 6 1 2 0).eval₂ order15Reduce (10:ZMod 1009)=(101:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 0 (by decide) 10 m coefficients 101
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At10

namespace At11
private def m : Array Nat := #[235313080530108606, 1013309916158556351, 730709039740288000, 249949983530287104, 441561875776274432, 335728178960007168]
private def l : Array Nat := #[1, 1880, 1925120, 1971322880, 2018634629120, 2067081860218880]
private def u : Array Nat := #[235313080530108606, 663155045130500096, 1086493410302361600, 622622852494917632, 276054384385720320, 506654958079180800]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(971:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 971 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[337, 756, 303, 469, 410, 42, 150]
theorem checked : (nodeMomentNorm 6 1 2 0).eval₂ order15Reduce (11:ZMod 1009)=(971:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 0 (by decide) 11 m coefficients 971
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At11

namespace At12
private def m : Array Nat := #[630503947831869739, 544935554912136383, 997547317776284672, 91198213703335936, 1064304371027673088, 632965754366459904]
private def l : Array Nat := #[1, 1136, 1163264, 1191182336, 1219770712064, 1249045209153536]
private def u : Array Nat := #[630503947831869739, 362539770003631104, 154248287550963712, 991918138977157120, 164710140375728128, 398568567022288896]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(291:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 291 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[874, 568, 381, 512, 592, 708, 633]
theorem checked : (nodeMomentNorm 6 1 2 0).eval₂ order15Reduce (12:ZMod 1009)=(291:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 0 (by decide) 12 m coefficients 291
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At12


def candidate : List Nat := [12, 589, 975, 246, 935, 516, 804, 76, 343, 465, 14, 911, 14]
private def values : Fin 13 → Nat := fun i => (#[12, 855, 941, 869, 877, 1004, 567, 497, 939, 237, 101, 971, 291] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 6 1 2 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=12)
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
  · decide +kernel

end

end RKCert.FixedPolynomial.FixedReplay.N6K1J2W0
