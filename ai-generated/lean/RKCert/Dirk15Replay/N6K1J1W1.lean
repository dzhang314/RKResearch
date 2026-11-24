module
public import RKCert.Dirk15Replay.Axes

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N6K1J1W1
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000
noncomputable section

namespace At0
private def m : Array Nat := #[97953291895308288, 313000174102250263, 404198066557312000, 69805795053666304, 738591188218544128, 773237049791610880]
private def l : Array Nat := #[1, 1024, 1048576, 1073741824, 1099511627776, 1125899906842624]
private def u : Array Nat := #[313000174102250263, 404198066557312000, 69805795053666304, 738591188218544128, 773237049791610880, 97953291895308288]
private def swaps : List (Fin 6×Fin 6) := [(4, 5), (3, 4), (2, 3), (1, 2), (0, 1)]
private theorem evaluated : (rowMatrix 1009 6 m).det=(452:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 452 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[977, 640, 645, 963, 327, 142, 334]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (0:ZMod 1009)=(452:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 0 m coefficients 452
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At0

namespace At1
private def m : Array Nat := #[860187528827765445, 323133273264559704, 256705179504173056, 109213052875833344, 185427782711377920, 919394030960246784]
private def l : Array Nat := #[1, 2031, 2079744, 2129657856, 2180769644544, 2233108116013056]
private def u : Array Nat := #[860187528827765445, 907475324915880960, 935622823329660928, 844425691414921216, 738243992726011904, 121597189939003392]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(252:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 252 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[1001, 240, 827, 728, 1002, 881, 334]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (1:ZMod 1009)=(252:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 1 m coefficients 252
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At1

namespace At2
private def m : Array Nat := #[1093248809544188095, 1124774006935977369, 772367336294736896, 363665875423723520, 252412025014059008, 660227045665538048]
private def l : Array Nat := #[1, 1528, 1564672, 1602224128, 1640677507072, 1680053767241728]
private def u : Array Nat := #[1093248809544188095, 1103381908705967104, 188025284642996224, 1025695020218318848, 197242490418364416, 190277084256403456]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(139:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 139 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[306, 824, 583, 426, 108, 876, 442]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (2:ZMod 1009)=(139:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 2 m coefficients 139
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At2

namespace At3
private def m : Array Nat := #[980658818859925968, 552816854260203738, 1060597712732514304, 78813491923779584, 263970985672179712, 336883765680799744]
private def l : Array Nat := #[1, 1629, 1668096, 1708130304, 1749125431296, 1791104441647104]
private def u : Array Nat := #[980658818859925968, 263460578201649152, 711568741611077632, 136234386944163840, 772877509489328128, 1100004208985243648]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(254:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 254 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[158, 169, 764, 768, 434, 31, 187]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (3:ZMod 1009)=(254:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 3 m coefficients 254
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At3

namespace At4
private def m : Array Nat := #[753227037677715975, 732960839355079707, 1098878309622639616, 620371405970604032, 239261455776481280, 756634424212193280]
private def l : Array Nat := #[1, 1339, 1371136, 1404043264, 1437740302336, 1472246069592064]
private def u : Array Nat := #[753227037677715975, 897342225754102784, 172262686291132416, 887209683863994368, 232506027344396288, 403072166649659392]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(249:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 249 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[760, 88, 786, 727, 179, 556, 351]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (4:ZMod 1009)=(249:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 4 m coefficients 249
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At4

namespace At5
private def m : Array Nat := #[538180155470774628, 504403158265860941, 541557855565460480, 263460961339310080, 777263269172740096, 810451120345317376]
private def l : Array Nat := #[1, 1409, 1442816, 1477443584, 1512902230016, 1549211883536384]
private def u : Array Nat := #[538180155470774628, 63050394783551488, 123848990125981696, 294986157844856832, 811039359066177536, 1119144507401568256]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(637:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 637 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[975, 175, 46, 186, 238, 330, 363]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (5:ZMod 1009)=(637:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 5 m coefficients 637
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At5

namespace At6
private def m : Array Nat := #[559572253700785112, 198158383605310094, 27021598796691456, 79939950633549824, 740798860464488448, 604201430672211968]
private def l : Array Nat := #[1, 1240, 1269760, 1300234240, 1331439861760, 1363394418442240]
private def u : Array Nat := #[559572253700785112, 886083226686152704, 622622649515769856, 781375591910735872, 96783411523354624, 380554168512806912]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(810:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 810 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[405, 586, 722, 202, 846, 263, 444]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (6:ZMod 1009)=(810:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 6 m coefficients 810
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At6

namespace At7
private def m : Array Nat := #[412079365904400769, 1016687615879284175, 328762773202222080, 501025872421060608, 190700893375561728, 253836552923250688]
private def l : Array Nat := #[1, 1151, 1178624, 1206910976, 1235876839424, 1265537883570176]
private def u : Array Nat := #[412079365904400769, 940126422213985280, 216172782517485568, 311874687586009088, 343822783563694080, 946881821654646784]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(94:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 94 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[799, 739, 858, 886, 697, 432, 431]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (7:ZMod 1009)=(94:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 7 m coefficients 94
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At7

namespace At8
private def m : Array Nat := #[674414044198732353, 573083052583486736, 376050569490743296, 1077486830682636288, 133490899274432512, 1006853583880060928]
private def l : Array Nat := #[1, 1995, 2042880, 2091909120, 2142114938880, 2193525697413120]
private def u : Array Nat := #[674414044198732353, 72057594038518784, 842173130923311104, 135108608370147328, 723462158402191360, 73183493944770560]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(558:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 558 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[736, 996, 941, 935, 556, 126, 325]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (8:ZMod 1009)=(558:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 8 m coefficients 558
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At8

namespace At9
private def m : Array Nat := #[1040331513922585127, 916482524170460241, 850054430244029440, 55169687151968256, 825890549595635712, 132945249449279488]
private def l : Array Nat := #[1, 1872, 1916928, 1962934272, 2010044694528, 2058285767196672]
private def u : Array Nat := #[1040331513922585127, 276971377083849728, 1125900484608000, 236439572068696064, 267444108828606464, 1060597712245751808]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(952:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 952 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[736, 264, 763, 834, 265, 791, 545]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (9:ZMod 1009)=(952:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 9 m coefficients 952
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At9

namespace At10
private def m : Array Nat := #[505529058172338483, 1065101311873437571, 748723438373178368, 607986280276426752, 434935879404879872, 51653956761288704]
private def l : Array Nat := #[1, 1280, 1310720, 1342177280, 1374389534720, 1407374883553280]
private def u : Array Nat := #[505529058172338483, 21392098230324224, 952511321510772736, 1012184345890258944, 331352122681458688, 513410357520236544]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(452:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 452 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[637, 614, 694, 647, 242, 776, 879]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (10:ZMod 1009)=(452:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 10 m coefficients 452
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At10

namespace At11
private def m : Array Nat := #[604608249974489942, 597852850534308548, 442478664285360128, 1033577032199438336, 352220514074230784, 553595308492193792]
private def l : Array Nat := #[1, 1065, 1090560, 1116733440, 1143535042560, 1170979883581440]
private def u : Array Nat := #[604608249974489942, 801640733672822784, 520165757856776192, 155375104119799808, 798076116974698496, 815151532554059776]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(618:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 618 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[337, 756, 303, 469, 410, 42, 150]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (11:ZMod 1009)=(618:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 11 m coefficients 618
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At11

namespace At12
private def m : Array Nat := #[195906583790616750, 1094374709451209221, 886083226868126720, 746471825609850880, 756796607545999360, 441921210993868800]
private def l : Array Nat := #[1, 1891, 1936384, 1982857216, 2030445789184, 2079176488124416]
private def u : Array Nat := #[195906583790616750, 512284457613572096, 924363823700246528, 226306068106444800, 1083307025405837312, 879327827244089344]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(552:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 552 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[874, 568, 381, 512, 592, 708, 633]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (12:ZMod 1009)=(552:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 12 m coefficients 552
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At12

namespace At13
private def m : Array Nat := #[964896220164129053, 165507286306157894, 12384899274446848, 510032964157964288, 710756552071446528, 311106815079219200]
private def l : Array Nat := #[1, 1188, 1216512, 1245708288, 1275605286912, 1306219813797888]
private def u : Array Nat := #[964896220164129053, 967148019978105856, 444730463501680640, 280349382820233216, 174827846374522880, 91197892454252544]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(474:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 474 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[799, 535, 294, 825, 354, 407, 70]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (13:ZMod 1009)=(474:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 13 m coefficients 474
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At13

namespace At14
private def m : Array Nat := #[783626335162466482, 81064793292851335, 966022120257756160, 341147863040917504, 1122718065146986496, 1274333976592384]
private def l : Array Nat := #[1, 1756, 1798144, 1841299456, 1885490642944, 1930742418374656]
private def u : Array Nat := #[783626335162466482, 163255486492362752, 746471638423306240, 355784561688313856, 840117043574341632, 908601224821997568]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(802:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 802 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[959, 134, 756, 648, 314, 650, 544]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (14:ZMod 1009)=(802:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 14 m coefficients 802
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At14

namespace At15
private def m : Array Nat := #[913104824449368926, 744219838423858105, 257831079571809280, 793760360888795136, 1018762318084833280, 794807268905320448]
private def l : Array Nat := #[1, 1649, 1688576, 1729101824, 1770600267776, 1813094674202624]
private def u : Array Nat := #[913104824449368926, 342273571681040384, 1047086914267512832, 719450966037889024, 95523371197923328, 757730637305085952]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(503:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 503 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[537, 210, 923, 427, 881, 937, 915]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (15:ZMod 1009)=(503:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 15 m coefficients 503
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At15

namespace At16
private def m : Array Nat := #[777996835628253503, 155374187144609530, 34902897447397376, 830914474572513280, 227783343582740480, 347614999167893504]
private def l : Array Nat := #[1, 1795, 1838080, 1882193920, 1927366574080, 1973623371857920]
private def u : Array Nat := #[777996835628253503, 145241087983025152, 521291657202630656, 1070731153930977280, 590322295394795520, 1027946614947315712]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(149:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 149 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[493, 262, 907, 436, 442, 813, 61]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (16:ZMod 1009)=(149:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 16 m coefficients 149
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At16

namespace At17
private def m : Array Nat := #[620370848670286391, 515662157334502971, 50665496403045376, 263461187611525120, 52415431914291200, 824786552948260864]
private def l : Array Nat := #[1, 1130, 1157120, 1184890880, 1213328261120, 1242448139386880]
private def u : Array Nat := #[620370848670286391, 646266546528246784, 844424930726510592, 501026067356581888, 337267495238893568, 356910270469111808]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(271:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 271 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[280, 729, 629, 42, 60, 788, 834]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (17:ZMod 1009)=(271:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 17 m coefficients 271
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At17

namespace At18
private def m : Array Nat := #[530298856122876501, 1079738010662688124, 1033576115107917824, 1101130750314414080, 259613795037478912, 196324398209171456]
private def l : Array Nat := #[1, 1219, 1248256, 1278214144, 1308891283456, 1340304674258944]
private def u : Array Nat := #[530298856122876501, 1050464613084779520, 678917644452102144, 492018900314095616, 878858335779028992, 487514659662856192]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(756:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 756 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[952, 186, 56, 640, 557, 103, 605]
theorem checked : (nodeMomentNorm 6 1 1 1).eval₂ order15Reduce (18:ZMod 1009)=(756:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 1 (by decide) 18 m coefficients 756
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At18


def candidate : List Nat := [452, 951, 549, 396, 600, 825, 490, 654, 110, 211, 86, 583, 209, 442, 410, 35, 508, 799, 14]
private def values : Fin 19 → Nat := fun i => (#[452, 252, 139, 254, 249, 637, 810, 94, 558, 952, 452, 618, 552, 474, 802, 503, 149, 271, 756] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 6 1 1 1).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=18)
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
    · exact At16.checked
    · exact At17.checked
    · exact At18.checked
  · decide +kernel

end

end RKCert.FixedPolynomial.FixedReplay.N6K1J1W1
