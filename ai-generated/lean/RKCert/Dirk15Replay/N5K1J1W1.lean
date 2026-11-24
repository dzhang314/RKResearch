module
public import RKCert.Dirk15Replay.Axes

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N5K1J1W1
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000
noncomputable section

namespace At0
private def m : Array Nat := #[152832116260864, 1035739953365783, 368336396114944, 299067992178688, 811189399453696]
private def l : Array Nat := #[1, 1024, 1048576, 1073741824, 1099511627776]
private def u : Array Nat := #[1035739953365783, 368336396114944, 299067992178688, 811189399453696, 152832116260864]
private def swaps : List (Fin 5×Fin 5) := [(3, 4), (2, 3), (1, 2), (0, 1)]
private theorem evaluated : (rowMatrix 1009 5 m).det=(294:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 294 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[320, 245, 793, 677, 332, 1001]
theorem checked : (nodeMomentNorm 5 1 1 1).eval₂ order15Reduce (0:ZMod 1009)=(294:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 1 1 (by decide) 0 m coefficients 294
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At0

namespace At1
private def m : Array Nat := #[249589139505861, 485984140203608, 827932999770112, 774818098053120, 1092459291475968]
private def l : Array Nat := #[1, 2031, 2079744, 2129657856, 2180769644544]
private def u : Array Nat := #[249589139505861, 985162419213312, 579443371278336, 824295492157440, 520068999938048]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(197:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 197 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[341, 904, 700, 93, 292, 8]
theorem checked : (nodeMomentNorm 5 1 1 1).eval₂ order15Reduce (1:ZMod 1009)=(197:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 1 1 (by decide) 1 m coefficients 197
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At1

namespace At2
private def m : Array Nat := #[49478023250111, 440904162934169, 603632084345856, 1026049862270976, 650250532421632]
private def l : Array Nat := #[1, 1528, 1564672, 1602224128, 1640677507072]
private def u : Array Nat := #[49478023250111, 1020346790771712, 4398246789120, 1028248456658944, 609129441787904]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(749:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 749 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[328, 860, 571, 612, 17, 161]
theorem checked : (nodeMomentNorm 5 1 1 1).eval₂ order15Reduce (2:ZMod 1009)=(749:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 1 1 (by decide) 2 m coefficients 749
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At2

namespace At3
private def m : Array Nat := #[712483534799312, 532163628318938, 269380835567616, 1108806165594112, 357575354744832]
private def l : Array Nat := #[1, 1629, 1668096, 1708130304, 1749125431296]
private def u : Array Nat := #[712483534799312, 1039038488723456, 684996230643712, 495278448705536, 555253372026880]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(686:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 686 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[969, 294, 670, 162, 541, 518]
theorem checked : (nodeMomentNorm 5 1 1 1).eval₂ order15Reduce (3:ZMod 1009)=(686:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 1 1 (by decide) 3 m coefficients 686
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At3

namespace At4
private def m : Array Nat := #[185817465094663, 1061028721335323, 413416916282368, 470048765378560, 889533897900032]
private def l : Array Nat := #[1, 1339, 1371136, 1404043264, 1437740302336]
private def u : Array Nat := #[185817465094663, 217703302831104, 620125102276608, 386485853356032, 247390116249600]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(363:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 363 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[928, 39, 584, 470, 607, 525]
theorem checked : (nodeMomentNorm 5 1 1 1).eval₂ order15Reduce (4:ZMod 1009)=(363:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 1 1 (by decide) 4 m coefficients 363
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At4

namespace At5
private def m : Array Nat := #[177021372072292, 579442628203341, 473889885729792, 600716486901760, 73475079274496]
private def l : Array Nat := #[1, 1409, 1442816, 1477443584, 1512902230016]
private def u : Array Nat := #[177021372072292, 100055558492160, 781753140641792, 275260159033344, 747667906887680]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(943:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 943 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[930, 600, 58, 434, 729, 611]
theorem checked : (nodeMomentNorm 5 1 1 1).eval₂ order15Reduce (5:ZMod 1009)=(943:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 1 1 (by decide) 5 m coefficients 943
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At5

namespace At6
private def m : Array Nat := #[538760697611224, 58274117280398, 208908241745920, 1098369852243968, 273381110841344]
private def l : Array Nat := #[1, 1240, 1269760, 1300234240, 1331439861760]
private def u : Array Nat := #[538760697611224, 173722838196224, 404621310820352, 234153027043328, 956575116165120]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(442:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 442 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[783, 165, 839, 594, 191, 765]
theorem checked : (nodeMomentNorm 5 1 1 1).eval₂ order15Reduce (6:ZMod 1009)=(442:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 1 1 (by decide) 6 m coefficients 442
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At6

namespace At7
private def m : Array Nat := #[1034640441737601, 329853488727503, 472790404119552, 233510341181440, 737169933074432]
private def l : Array Nat := #[1, 1151, 1178624, 1206910976, 1235876839424]
private def u : Array Nat := #[1034640441737601, 949978046792704, 750966845472768, 269793739407360, 916992697565184]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(294:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 294 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[436, 688, 448, 540, 100, 122]
theorem checked : (nodeMomentNorm 5 1 1 1).eval₂ order15Reduce (7:ZMod 1009)=(294:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 1 1 (by decide) 7 m coefficients 294
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At7

namespace At8
private def m : Array Nat := #[501377302266433, 570646535406864, 1079721023782912, 35804206333952, 830423336747008]
private def l : Array Nat := #[1, 1995, 2042880, 2091909120, 2142114938880]
private def u : Array Nat := #[501377302266433, 763061070267392, 122046395711488, 235915037376512, 896101976637440]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(802:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 802 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[28, 855, 78, 356, 385, 585]
theorem checked : (nodeMomentNorm 5 1 1 1).eval₂ order15Reduce (8:ZMod 1009)=(802:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 1 1 (by decide) 8 m coefficients 802
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At8

namespace At9
private def m : Array Nat := #[63771674411559, 42880954047569, 192415112709120, 341440321290240, 179307368415232]
private def l : Array Nat := #[1, 1872, 1916928, 1962934272, 2010044694528]
private def u : Array Nat := #[63771674411559, 325455442385920, 448601321897984, 454689934016512, 68169720922112]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(724:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 724 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[946, 149, 384, 46, 832, 357]
theorem checked : (nodeMomentNorm 5 1 1 1).eval₂ order15Reduce (9:ZMod 1009)=(724:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 1 1 (by decide) 9 m coefficients 724
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At9

namespace At10
private def m : Array Nat := #[417814418555187, 876310767652739, 782852601809920, 688624860397568, 583706456621056]
private def l : Array Nat := #[1, 1280, 1310720, 1342177280, 1374389534720]
private def u : Array Nat := #[417814418555187, 418913930497024, 43980787023872, 523697173561344, 838927371993088]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(441:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 441 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[829, 897, 300, 978, 101, 590]
theorem checked : (nodeMomentNorm 5 1 1 1).eval₂ order15Reduce (10:ZMod 1009)=(441:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 1 1 (by decide) 10 m coefficients 441
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At10

namespace At11
private def m : Array Nat := #[947779023143766, 796046419385028, 867515570524160, 60291345809408, 139298674311168]
private def l : Array Nat := #[1, 1065, 1090560, 1116733440, 1143535042560]
private def u : Array Nat := #[947779023143766, 766359605434368, 510174290771968, 221918812700672, 1062128232431616]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(312:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 312 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[680, 227, 901, 265, 797, 935]
theorem checked : (nodeMomentNorm 5 1 1 1).eval₂ order15Reduce (11:ZMod 1009)=(312:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 1 1 (by decide) 11 m coefficients 312
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At11

namespace At12
private def m : Array Nat := #[677299162710190, 203409651317253, 799345136374784, 21078094118912, 1092370170904576]
private def l : Array Nat := #[1, 1891, 1936384, 1982857216, 2030445789184]
private def u : Array Nat := #[677299162710190, 970868767504384, 1096213275344896, 366324203126784, 941181953376256]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(546:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 546 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[879, 187, 184, 281, 415, 137]
theorem checked : (nodeMomentNorm 5 1 1 1).eval₂ order15Reduce (12:ZMod 1009)=(546:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 1 1 (by decide) 12 m coefficients 546
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At12

namespace At13
private def m : Array Nat := #[1054431651037469, 312261302580550, 990660275804160, 170730660560896, 771107690905600]
private def l : Array Nat := #[1, 1188, 1216512, 1245708288, 1275605286912]
private def u : Array Nat := #[1054431651037469, 452998790935552, 1029143182442496, 21196737347584, 672901116198912]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(153:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 153 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[223, 711, 966, 15, 447, 666]
theorem checked : (nodeMomentNorm 5 1 1 1).eval₂ order15Reduce (13:ZMod 1009)=(153:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 1 1 (by decide) 13 m coefficients 153
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At13

namespace At14
private def m : Array Nat := #[586039697604786, 106652628076679, 51677233290240, 309154035007488, 430054001606656]
private def l : Array Nat := #[1, 1756, 1798144, 1841299456, 1885490642944]
private def u : Array Nat := #[586039697604786, 466192930359296, 495879930773504, 101346195800064, 714682558054400]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(265:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 265 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[11, 657, 620, 551, 354, 231]
theorem checked : (nodeMomentNorm 5 1 1 1).eval₂ order15Reduce (14:ZMod 1009)=(265:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 1 1 (by decide) 14 m coefficients 265
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At14

namespace At15
private def m : Array Nat := #[181419418583902, 995058024020921, 1100416476160, 466019983294464, 258308996857856]
private def l : Array Nat := #[1, 1649, 1688576, 1729101824, 1770600267776]
private def u : Array Nat := #[181419418583902, 767459117070336, 712484438671360, 36109937541120, 455197813899264]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(198:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 198 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[57, 863, 991, 458, 619, 447]
theorem checked : (nodeMomentNorm 5 1 1 1).eval₂ order15Reduce (15:ZMod 1009)=(198:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 1 1 (by decide) 15 m coefficients 198
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At15


def candidate : List Nat := [294, 751, 255, 235, 937, 661, 161, 618, 712, 245, 837, 330, 942, 50, 647, 594]
private def values : Fin 16 → Nat := fun i => (#[294, 197, 749, 686, 363, 943, 442, 294, 802, 724, 441, 312, 546, 153, 265, 198] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 5 1 1 1).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=15)
    (by decide) ((nodeMomentNorm_degree (by decide) (by decide) 1 1).trans (by decide)) (by decide) values
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
  · decide +kernel

end

end RKCert.FixedPolynomial.FixedReplay.N5K1J1W1
