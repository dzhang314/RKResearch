module
public import RKCert.Dirk15Replay.Axes

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N5K1J2W1
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000
noncomputable section

namespace At0
private def m : Array Nat := #[471690488315904, 690493302243519, 985162418682880, 938983130398720, 170629386993664]
private def l : Array Nat := #[1, 1024, 1048576, 1073741824, 1099511627776]
private def u : Array Nat := #[690493302243519, 985162418682880, 938983130398720, 170629386993664, 471690488315904]
private def swaps : List (Fin 5×Fin 5) := [(3, 4), (2, 3), (1, 2), (0, 1)]
private theorem evaluated : (rowMatrix 1009 5 m).det=(101:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 101 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[320, 245, 793, 677, 332, 1001]
theorem checked : (nodeMomentNorm 5 1 2 1).eval₂ order15Reduce (0:ZMod 1009)=(101:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 2 1 (by decide) 0 m coefficients 101
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At0

namespace At1
private def m : Array Nat := #[679498185966397, 242992070587692, 968670613647360, 387918539522048, 837050471284736]
private def l : Array Nat := #[1, 1695, 1735680, 1777336320, 1819992391680]
private def u : Array Nat := #[679498185966397, 266081814770688, 1042337892401152, 1015739364409344, 1048934092898304]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(236:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 236 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[341, 904, 700, 93, 292, 8]
theorem checked : (nodeMomentNorm 5 1 2 1).eval₂ order15Reduce (1:ZMod 1009)=(236:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 2 1 (by decide) 1 m coefficients 236
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At1

namespace At2
private def m : Array Nat := #[49478023249991, 440904162811289, 603631958516736, 1025921013252096, 486423299883008]
private def l : Array Nat := #[1, 1584, 1622016, 1660944384, 1700807049216]
private def u : Array Nat := #[49478023249991, 468391953505280, 124244888387584, 232073189130240, 368336395304960]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(315:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 315 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[328, 860, 571, 612, 17, 161]
theorem checked : (nodeMomentNorm 5 1 2 1).eval₂ order15Reduce (2:ZMod 1009)=(315:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 2 1 (by decide) 2 m coefficients 315
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At2

namespace At3
private def m : Array Nat := #[593736278999793, 73667279832582, 39583208708096, 924398838087680, 928544012107776]
private def l : Array Nat := #[1, 1424, 1458176, 1493172224, 1529008357376]
private def u : Array Nat := #[593736278999793, 1101710651802624, 899401301098496, 612136992636928, 466192930177024]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(952:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 952 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[969, 294, 670, 162, 541, 518]
theorem checked : (nodeMomentNorm 5 1 2 1).eval₂ order15Reduce (3:ZMod 1009)=(952:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 2 1 (by decide) 3 m coefficients 952
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At3

namespace At4
private def m : Array Nat := #[370535418561369, 848822977521267, 108852550421504, 1042158365704192, 796719654633472]
private def l : Array Nat := #[1, 1146, 1173504, 1201668096, 1230508130304]
private def u : Array Nat := #[370535418561369, 19791210177536, 1022546712461312, 545178452492288, 960973162676224]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(565:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 565 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[928, 39, 584, 470, 607, 525]
theorem checked : (nodeMomentNorm 5 1 2 1).eval₂ order15Reduce (4:ZMod 1009)=(565:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 2 1 (by decide) 4 m coefficients 565
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At4

namespace At5
private def m : Array Nat := #[693791837127039, 376032977092320, 768559030173696, 472102503186432, 186607739076608]
private def l : Array Nat := #[1, 1674, 1714176, 1755316224, 1797443813376]
private def u : Array Nat := #[693791837127039, 940082442140672, 998356959625216, 543569987239936, 1033540930109440]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(292:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 292 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[930, 600, 58, 434, 729, 611]
theorem checked : (nodeMomentNorm 5 1 2 1).eval₂ order15Reduce (5:ZMod 1009)=(292:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 2 1 (by decide) 5 m coefficients 292
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At5

namespace At6
private def m : Array Nat := #[295768627872084, 908196604891981, 409018682913792, 607296376799232, 915700986150912]
private def l : Array Nat := #[1, 1071, 1096704, 1123024896, 1149977493504]
private def u : Array Nat := #[295768627872084, 319957884030976, 902699402919936, 337915141947392, 581641651093504]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(162:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 162 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[783, 165, 839, 594, 191, 765]
theorem checked : (nodeMomentNorm 5 1 2 1).eval₂ order15Reduce (6:ZMod 1009)=(162:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 2 1 (by decide) 6 m coefficients 162
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At6

namespace At7
private def m : Array Nat := #[849922488271576, 557452396028858, 466193694517248, 483468288983040, 527690419404800]
private def l : Array Nat := #[1, 1333, 1364992, 1397751808, 1431297851392]
private def u : Array Nat := #[849922488271576, 860917605294080, 700389670256640, 397705381675008, 1021446302203904]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(391:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 391 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[436, 688, 448, 540, 100, 122]
theorem checked : (nodeMomentNorm 5 1 2 1).eval₂ order15Reduce (7:ZMod 1009)=(391:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 2 1 (by decide) 7 m coefficients 391
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At7

namespace At8
private def m : Array Nat := #[556352883655194, 268280837728310, 915893750126592, 1051710845878272, 353001214574592]
private def l : Array Nat := #[1, 1628, 1667072, 1707081728, 1748051689472]
private def u : Array Nat := #[556352883655194, 381530535389184, 118747819933696, 330431161434112, 814738116182016]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(160:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 160 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[28, 855, 78, 356, 385, 585]
theorem checked : (nodeMomentNorm 5 1 2 1).eval₂ order15Reduce (8:ZMod 1009)=(160:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 2 1 (by decide) 8 m coefficients 160
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At8

namespace At9
private def m : Array Nat := #[196812581372683, 1031341907651747, 1072024654089216, 631956290142208, 239868554772480]
private def l : Array Nat := #[1, 1054, 1079296, 1105199104, 1131723882496]
private def u : Array Nat := #[196812581372683, 674000628624384, 821336002789376, 398859654135808, 502476813893632]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(434:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 434 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[946, 149, 384, 46, 832, 357]
theorem checked : (nodeMomentNorm 5 1 2 1).eval₂ order15Reduce (9:ZMod 1009)=(434:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 2 1 (by decide) 9 m coefficients 434
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At9

namespace At10
private def m : Array Nat := #[580542139466170, 213305256241424, 141837463732224, 396299065098240, 252080220536832]
private def l : Array Nat := #[1, 1956, 2002944, 2051014656, 2100239007744]
private def u : Array Nat := #[580542139466170, 538760698062848, 578343579680768, 552429431029760, 594835790626816]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(724:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 724 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[829, 897, 300, 978, 101, 590]
theorem checked : (nodeMomentNorm 5 1 2 1).eval₂ order15Reduce (10:ZMod 1009)=(724:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 2 1 (by decide) 10 m coefficients 724
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At10

namespace At11
private def m : Array Nat := #[256186209272344, 315559837720957, 866415725114368, 1038514901745664, 822843793211392]
private def l : Array Nat := #[1, 1949, 1995776, 2043674624, 2092722814976]
private def u : Array Nat := #[256186209272344, 756464000458752, 63772236447744, 848298990632960, 1029142883598336]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(771:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 771 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[680, 227, 901, 265, 797, 935]
theorem checked : (nodeMomentNorm 5 1 2 1).eval₂ order15Reduce (11:ZMod 1009)=(771:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 2 1 (by decide) 11 m coefficients 771
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At11

namespace At12
private def m : Array Nat := #[146235046494260, 207807697703402, 714682613082112, 597091162259456, 582167784587264]
private def l : Array Nat := #[1, 1926, 1972224, 2019557376, 2068026753024]
private def u : Array Nat := #[146235046494260, 323256418619392, 911495193952256, 499234113585152, 742170348748800]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(938:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 938 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[879, 187, 184, 281, 415, 137]
theorem checked : (nodeMomentNorm 5 1 2 1).eval₂ order15Reduce (12:ZMod 1009)=(938:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 2 1 (by decide) 12 m coefficients 938
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At12

namespace At13
private def m : Array Nat := #[681697209222128, 1009351675331159, 584941243554816, 106636076122112, 1082562613084160]
private def l : Array Nat := #[1, 1434, 1468416, 1503657984, 1539745775616]
private def u : Array Nat := #[681697209222128, 1084118466019328, 968670801035264, 119829587558400, 100055558127616]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(91:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 91 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[223, 711, 966, 15, 447, 666]
theorem checked : (nodeMomentNorm 5 1 2 1).eval₂ order15Reduce (13:ZMod 1009)=(91:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 2 1 (by decide) 13 m coefficients 91
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At13

namespace At14
private def m : Array Nat := #[312261302288761, 1101710651418308, 1059929605214208, 412722403475456, 1014509930020864]
private def l : Array Nat := #[1, 1885, 1930240, 1976565760, 2024003338240]
private def u : Array Nat := #[312261302288761, 721279628207104, 196812976685056, 696395661049856, 845524441759744]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(967:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 967 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[11, 657, 620, 551, 354, 231]
theorem checked : (nodeMomentNorm 5 1 2 1).eval₂ order15Reduce (14:ZMod 1009)=(967:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 2 1 (by decide) 14 m coefficients 967
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At14

namespace At15
private def m : Array Nat := #[938982930120881, 241892558292785, 637716930544640, 168416188039168, 224078107508736]
private def l : Array Nat := #[1, 1878, 1923072, 1969225728, 2016487145472]
private def u : Array Nat := #[938982930120881, 451899279197184, 789449534341120, 498268819685376, 876310767337472]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(734:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 734 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[57, 863, 991, 458, 619, 447]
theorem checked : (nodeMomentNorm 5 1 2 1).eval₂ order15Reduce (15:ZMod 1009)=(734:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K1 2 1 (by decide) 15 m coefficients 734
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At15


def candidate : List Nat := [101, 1006, 35, 942, 321, 550, 649, 931, 197, 304, 984, 428, 410, 830, 735, 894]
private def values : Fin 16 → Nat := fun i => (#[101, 236, 315, 952, 565, 292, 162, 391, 160, 434, 724, 771, 938, 91, 967, 734] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 5 1 2 1).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=15)
    (by decide) ((nodeMomentNorm_degree (by decide) (by decide) 2 1).trans (by decide)) (by decide) values
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

end RKCert.FixedPolynomial.FixedReplay.N5K1J2W1
