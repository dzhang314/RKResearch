module
public import RKCert.Dirk15Replay.Axes

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N5K1J3W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000
noncomputable section

namespace At0
private def m : Array Nat := #[631119674343424, 517869976683396, 738871814787072, 149534525095936, 960840018690048]
private def l : Array Nat := #[1, 1024, 1048576, 1073741824, 1099511627776]
private def u : Array Nat := #[517869976683396, 738871814787072, 149534525095936, 960840018690048, 631119674343424]
private def swaps : List (Fin 5×Fin 5) := [(3, 4), (2, 3), (1, 2), (0, 1)]
private theorem evaluated : (rowMatrix 1009 5 m).det=(829:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 829 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[320, 245, 793, 677, 332, 1001]
theorem checked : (nodeMomentNorm 5 1 3 0).eval₂ order15Reduce (0:ZMod 1009)=(829:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 3 0 (by decide) 0 m coefficients 829
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At0

namespace At1
private def m : Array Nat := #[929087325471009, 728976209512324, 687195071320064, 51988301611008, 927854669856768]
private def l : Array Nat := #[1, 1275, 1305600, 1336934400, 1369020825600]
private def u : Array Nat := #[929087325471009, 503576325817344, 761961861087232, 727087497347072, 448600744132608]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(131:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 131 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[341, 904, 700, 93, 292, 8]
theorem checked : (nodeMomentNorm 5 1 3 0).eval₂ order15Reduce (1:ZMod 1009)=(131:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 3 0 (by decide) 1 m coefficients 131
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At1

namespace At2
private def m : Array Nat := #[480486581338690, 1002754605124484, 758663630163968, 125965892059136, 72434623447040]
private def l : Array Nat := #[1, 1654, 1693696, 1734344704, 1775968976896]
private def u : Array Nat := #[480486581338690, 54975581980672, 515671559503872, 309583390179328, 680597697593344]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(608:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 608 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[328, 860, 571, 612, 17, 161]
theorem checked : (nodeMomentNorm 5 1 3 0).eval₂ order15Reduce (2:ZMod 1009)=(608:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 3 0 (by decide) 2 m coefficients 608
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At2

namespace At3
private def m : Array Nat := #[753165465027427, 843325419392900, 420014351847424, 556185249906688, 603498739662848]
private def l : Array Nat := #[1, 1444, 1478656, 1514143744, 1550483193856]
private def u : Array Nat := #[753165465027427, 694891349642240, 339750002098176, 975098236370944, 823534209204224]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(34:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 34 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[969, 294, 670, 162, 541, 518]
theorem checked : (nodeMomentNorm 5 1 3 0).eval₂ order15Reduce (3:ZMod 1009)=(34:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 3 0 (by decide) 3 m coefficients 34
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At3

namespace At4
private def m : Array Nat := #[277076930199699, 236395000123268, 97856689934336, 857777853431808, 66937065308160]
private def l : Array Nat := #[1, 1339, 1371136, 1404043264, 1437740302336]
private def u : Array Nat := #[277076930199699, 600333348916224, 701488572661760, 660964328341504, 480486581338112]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(209:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 209 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[928, 39, 584, 470, 607, 525]
theorem checked : (nodeMomentNorm 5 1 3 0).eval₂ order15Reduce (4:ZMod 1009)=(209:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 3 0 (by decide) 4 m coefficients 209
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At4

namespace At5
private def m : Array Nat := #[516770465055156, 905997581734788, 294669574344704, 981233467129856, 857485925679104]
private def l : Array Nat := #[1, 1276, 1306624, 1337982976, 1370094567424]
private def u : Array Nat := #[516770465055156, 480486581784576, 137439410651136, 738240453672960, 208907209277440]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(434:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 434 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[930, 600, 58, 434, 729, 611]
theorem checked : (nodeMomentNorm 5 1 3 0).eval₂ order15Reduce (5:ZMod 1009)=(434:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 3 0 (by decide) 5 m coefficients 434
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At5

namespace At6
private def m : Array Nat := #[649811372016341, 914793675052932, 704787714543616, 187696383262720, 346213018763264]
private def l : Array Nat := #[1, 1234, 1263616, 1293942784, 1324997410816]
private def u : Array Nat := #[649811372016341, 911495140168704, 108852411367424, 626400579026944, 984062906859520]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(223:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 223 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[783, 165, 839, 594, 191, 765]
theorem checked : (nodeMomentNorm 5 1 3 0).eval₂ order15Reduce (6:ZMod 1009)=(223:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 3 0 (by decide) 6 m coefficients 223
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At6

namespace At7
private def m : Array Nat := #[111050674405381, 358440790660996, 439804657274880, 371641242615808, 452865646657536]
private def l : Array Nat := #[1, 1204, 1232896, 1262485504, 1292785156096]
private def u : Array Nat := #[111050674405381, 338649581360128, 500277795880960, 183623810547712, 682796720848896]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(669:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 669 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[436, 688, 448, 540, 100, 122]
theorem checked : (nodeMomentNorm 5 1 3 0).eval₂ order15Reduce (7:ZMod 1009)=(669:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 3 0 (by decide) 7 m coefficients 669
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At7

namespace At8
private def m : Array Nat := #[27487790694694, 403520767695748, 472790309146624, 508290995847168, 52643414147072]
private def l : Array Nat := #[1, 1686, 1726464, 1767899136, 1810328715264]
private def u : Array Nat := #[27487790694694, 1066526279243776, 15393471070208, 302681377734656, 688294278987776]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(842:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 842 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[28, 855, 78, 356, 385, 585]
theorem checked : (nodeMomentNorm 5 1 3 0).eval₂ order15Reduce (8:ZMod 1009)=(842:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 3 0 (by decide) 8 m coefficients 842
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At8

namespace At9
private def m : Array Nat := #[215504279044679, 106652628492164, 535462774968320, 1075949307166720, 171390669946880]
private def l : Array Nat := #[1, 1164, 1191936, 1220542464, 1249835483136]
private def u : Array Nat := #[215504279044679, 999456070245376, 396924308946944, 976992316948480, 1045635558014976]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(40:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 40 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[946, 149, 384, 46, 832, 357]
theorem checked : (nodeMomentNorm 5 1 3 0).eval₂ order15Reduce (9:ZMod 1009)=(40:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 3 0 (by decide) 9 m coefficients 40
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At9

namespace At10
private def m : Array Nat := #[615726511555432, 999456070542212, 452999705923584, 723316386037760, 890471274512384]
private def l : Array Nat := #[1, 1150, 1177600, 1205862400, 1234803097600]
private def u : Array Nat := #[615726511555432, 1076421884485632, 171524728291328, 190052302848000, 358440790654976]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(996:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 996 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[829, 897, 300, 978, 101, 590]
theorem checked : (nodeMomentNorm 5 1 3 0).eval₂ order15Reduce (10:ZMod 1009)=(996:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 3 0 (by decide) 10 m coefficients 996
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At10


def candidate : List Nat := [829, 824, 671, 563, 125, 658, 776, 226, 153, 236, 115]
private def values : Fin 11 → Nat := fun i => (#[829, 131, 608, 34, 209, 434, 223, 669, 842, 40, 996] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 5 1 3 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=10)
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
  · decide +kernel

end

end RKCert.FixedPolynomial.FixedReplay.N5K1J3W0
