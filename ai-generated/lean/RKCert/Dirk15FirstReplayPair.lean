module
public import RKCert.Dirk15SampleMatrix

@[expose] public section

/-! # One complete exact modular replay pair for order 15 -/
namespace RKCert.FixedPolynomial.Order15Smoke
open Polynomial RKCert.LU RKCert.Compound RKCert.GoodPrimeDense

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace J1
namespace S0
private def m:Array Nat:=#[152832116260864, 1035739953365783, 368336396114944, 299067992178688, 811189399453696]
private def l:Array Nat:=#[1, 1024, 1048576, 1073741824, 1099511627776]
private def u:Array Nat:=#[1035739953365783, 368336396114944, 299067992178688, 811189399453696, 152832116260864]
private def w:List (Fin 5×Fin 5):=[(3, 4), (2, 3), (1, 2), (0, 1)]
private theorem determinant:(rowMatrix 1009 5 m).det=(294:ZMod 1009):=
  det_packed_compact 1009 m l u w 294 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 1 0).eval₂ order15Reduce (0:ZMod 1009)=(294:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 1 0 0 m 294
    (by decide +kernel) determinant
end S0
namespace S1
private def m:Array Nat:=#[748767418516274, 348545186843415, 264983160839168, 104233243246592, 637466562265088]
private def l:Array Nat:=#[1, 1527, 1563648, 1601175552, 1639603765248]
private def u:Array Nat:=#[748767418516274, 916992698402816, 531064973950976, 346124971933696, 45079976738816]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(600:ZMod 1009):=
  det_packed_compact 1009 m l u w 600 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 1 0).eval₂ order15Reduce (1:ZMod 1009)=(600:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 1 0 1 m 600
    (by decide +kernel) determinant
end S1
namespace S2
private def m:Array Nat:=#[960973162676851, 896101977280279, 407919472172032, 251362716680192, 799094771548160]
private def l:Array Nat:=#[1, 1780, 1822720, 1866465280, 1911260446720]
private def u:Array Nat:=#[960973162676851, 1062128233073664, 649812029472768, 461368608161792, 866415162687488]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(574:ZMod 1009):=
  det_packed_compact 1009 m l u w 574 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 1 0).eval₂ order15Reduce (2:ZMod 1009)=(574:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 1 0 2 m 574
    (by decide +kernel) determinant
end S2
namespace S3
private def m:Array Nat:=#[396923697627572, 577243605029655, 840027341609984, 1568492486656, 799094771548160]
private def l:Array Nat:=#[1, 1528, 1564672, 1602224128, 1640677507072]
private def u:Array Nat:=#[396923697627572, 221001837629440, 395824643178496, 199479756062720, 343047627866112]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(171:ZMod 1009):=
  det_packed_compact 1009 m l u w 171 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 1 0).eval₂ order15Reduce (3:ZMod 1009)=(171:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 1 0 3 m 171
    (by decide +kernel) determinant
end S3
namespace S4
private def m:Array Nat:=#[554153860399349, 472790000195351, 195713327455232, 606094803075072, 692442143653888]
private def l:Array Nat:=#[1, 1402, 1435648, 1470103552, 1505386037248]
private def u:Array Nat:=#[554153860399349, 680597697844224, 312261559189504, 168488345796608, 338649581355008]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(660:ZMod 1009):=
  det_packed_compact 1009 m l u w 660 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 1 0).eval₂ order15Reduce (4:ZMod 1009)=(660:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 1 0 4 m 660
    (by decide +kernel) determinant
end S4
namespace S5
private def m:Array Nat:=#[1033540930109494, 702587930204951, 589338289921024, 852180323008512, 227348725104640]
private def l:Array Nat:=#[1, 1730, 1771520, 1814036480, 1857573355520]
private def u:Array Nat:=#[1033540930109494, 1012650209236992, 116548289167360, 665262516862976, 980764371976192]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(304:ZMod 1009):=
  det_packed_compact 1009 m l u w 304 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 1 0).eval₂ order15Reduce (5:ZMod 1009)=(304:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 1 0 5 m 304
    (by decide +kernel) determinant
end S5
namespace S6
private def m:Array Nat:=#[190215511606120, 720180117086999, 300167589551104, 374771085737984, 440653980893184]
private def l:Array Nat:=#[1, 1276, 1306624, 1337982976, 1370094567424]
private def u:Array Nat:=#[190215511606120, 490382186881024, 977466751451136, 341784907481088, 1079720418476032]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(617:ZMod 1009):=
  det_packed_compact 1009 m l u w 617 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 1 0).eval₂ order15Reduce (6:ZMod 1009)=(617:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 1 0 6 m 617
    (by decide +kernel) determinant
end S6
namespace S7
private def m:Array Nat:=#[222101348811433, 716881582008087, 879610017111040, 744001907982336, 1050882934308864]
private def l:Array Nat:=#[1, 1240, 1269760, 1300234240, 1331439861760]
private def u:Array Nat:=#[222101348811433, 447501233202176, 737773016317952, 30418032132096, 184717953466368]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(444:ZMod 1009):=
  det_packed_compact 1009 m l u w 444 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 1 0).eval₂ order15Reduce (7:ZMod 1009)=(444:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 1 0 7 m 444
    (by decide +kernel) determinant
end S7
namespace S8
private def m:Array Nat:=#[54975581389290, 807041535290135, 945580514499584, 1016475706982400, 305414050676736]
private def l:Array Nat:=#[1, 1213, 1242112, 1271922688, 1302448832512]
private def u:Array Nat:=#[54975581389290, 401321744640000, 535462676529152, 770184272936960, 171523813933056]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(736:ZMod 1009):=
  det_packed_compact 1009 m l u w 736 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 1 0).eval₂ order15Reduce (8:ZMod 1009)=(736:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 1 0 8 m 736
    (by decide +kernel) determinant
end S8
namespace S9
private def m:Array Nat:=#[431008558088491, 213305256095511, 1070924639788032, 1041559389732864, 609978771570688]
private def l:Array Nat:=#[1, 1192, 1220608, 1249902592, 1279900254208]
private def u:Array Nat:=#[431008558088491, 1024744837393408, 871913034350592, 1001976141709312, 960973162676224]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(672:ZMod 1009):=
  det_packed_compact 1009 m l u w 672 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 1 0).eval₂ order15Reduce (9:ZMod 1009)=(672:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 1 0 9 m 672
    (by decide +kernel) determinant
end S9
namespace S10
private def m:Array Nat:=#[122045790683244, 889504906982167, 905997695343616, 335467840012288, 1080569748258816]
private def l:Array Nat:=#[1, 1377, 1410048, 1443889152, 1478542491648]
private def u:Array Nat:=#[122045790683244, 1074222860447744, 13194252779520, 115564685033472, 264982302294016]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(2:ZMod 1009):=
  det_packed_compact 1009 m l u w 2 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 1 0).eval₂ order15Reduce (10:ZMod 1009)=(2:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 1 0 10 m 2
    (by decide +kernel) determinant
end S10
def candidate:List Nat:=[294, 722, 101, 89, 400, 3, 801, 724, 805, 61, 636]
private def values:Fin 11→Nat:=fun i=>(#[294, 600, 574, 171, 660, 304, 617, 444, 736, 672, 2]:Array Nat)[i.val]!
theorem exactReduction:(nodeMomentNorm 5 1 1 0).map order15Reduce=residuePoly candidate:=by
  apply integer_reduction_of_residue_samples _ _ (d:=10) (by decide)
    ((nodeMomentNorm_degree (by decide) (by decide) 1 0).trans (by decide)) (by decide) values
  · intro i
    rw [eval_map]
    fin_cases i
    · exact S0.verified
    · exact S1.verified
    · exact S2.verified
    · exact S3.verified
    · exact S4.verified
    · exact S5.verified
    · exact S6.verified
    · exact S7.verified
    · exact S8.verified
    · exact S9.verified
    · exact S10.verified
  · decide +kernel
end J1

namespace J2
namespace S0
private def m:Array Nat:=#[471690488315904, 690493302243519, 985162418682880, 938983130398720, 170629386993664]
private def l:Array Nat:=#[1, 1024, 1048576, 1073741824, 1099511627776]
private def u:Array Nat:=#[690493302243519, 985162418682880, 938983130398720, 170629386993664, 471690488315904]
private def w:List (Fin 5×Fin 5):=[(3, 4), (2, 3), (1, 2), (0, 1)]
private theorem determinant:(rowMatrix 1009 5 m).det=(101:ZMod 1009):=
  det_packed_compact 1009 m l u w 101 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 2 0).eval₂ order15Reduce (0:ZMod 1009)=(101:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 2 0 0 m 101
    (by decide +kernel) determinant
end S0
namespace S1
private def m:Array Nat:=#[499178279010413, 971968279065791, 546457393495040, 438822377619456, 654414503215104]
private def l:Array Nat:=#[1, 1359, 1391616, 1425014784, 1459215138816]
private def u:Array Nat:=#[499178279010413, 158329674511360, 757563625832448, 709302037774336, 490382185988096]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(950:ZMod 1009):=
  det_packed_compact 1009 m l u w 950 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 2 0).eval₂ order15Reduce (1:ZMod 1009)=(950:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 2 0 1 m 950
    (by decide +kernel) determinant
end S1
namespace S2
private def m:Array Nat:=#[1010451185926362, 227598907173055, 1011550926339072, 167360043417600, 629125735776256]
private def l:Array Nat:=#[1, 1696, 1736704, 1778384896, 1821066133504]
private def u:Array Nat:=#[1010451185926362, 161628209506304, 9895833239552, 173956912906240, 374933465071616]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(518:ZMod 1009):=
  det_packed_compact 1009 m l u w 518 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 2 0).eval₂ order15Reduce (2:ZMod 1009)=(518:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 2 0 2 m 518
    (by decide +kernel) determinant
end S2
namespace S3
private def m:Array Nat:=#[634418209227079, 384829070056639, 190215854685184, 370886732414976, 516975549743104]
private def l:Array Nat:=#[1, 1472, 1507328, 1543503872, 1580547964928]
private def u:Array Nat:=#[634418209227079, 173722837523456, 20891063812096, 996508648341504, 219902325555200]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(893:ZMod 1009):=
  det_packed_compact 1009 m l u w 893 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 2 0).eval₂ order15Reduce (3:ZMod 1009)=(893:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 2 0 3 m 893
    (by decide +kernel) determinant
end S3
namespace S4
private def m:Array Nat:=#[369435906933172, 684995744551103, 500278248012800, 34553212174336, 1060134293864448]
private def l:Array Nat:=#[1, 1360, 1392640, 1426063360, 1460288880640]
private def u:Array Nat:=#[369435906933172, 808141046861824, 769658596622336, 1030710546661376, 1033540930109440]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(554:ZMod 1009):=
  det_packed_compact 1009 m l u w 554 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 2 0).eval₂ order15Reduce (4:ZMod 1009)=(554:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 2 0 4 m 554
    (by decide +kernel) determinant
end S4
namespace S5
private def m:Array Nat:=#[1058829697548833, 468391953990847, 23090315852800, 938468808065024, 30991410266112]
private def l:Array Nat:=#[1, 1091, 1117184, 1143996416, 1171452329984]
private def u:Array Nat:=#[1058829697548833, 528865093518336, 90160524951552, 444787886915584, 223200860438528]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(32:ZMod 1009):=
  det_packed_compact 1009 m l u w 32 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 2 0).eval₂ order15Reduce (5:ZMod 1009)=(32:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 2 0 5 m 32
    (by decide +kernel) determinant
end S5
namespace S6
private def m:Array Nat:=#[866415162688142, 849922488940735, 200111802219520, 619727473868800, 767664200876032]
private def l:Array Nat:=#[1, 1248, 1277952, 1308622848, 1340029796352]
private def u:Array Nat:=#[866415162688142, 919191721490432, 650911569412096, 148036785274880, 1046735069642752]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(85:ZMod 1009):=
  det_packed_compact 1009 m l u w 85 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 2 0).eval₂ order15Reduce (6:ZMod 1009)=(85:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 2 0 6 m 85
    (by decide +kernel) determinant
end S6
namespace S7
private def m:Array Nat:=#[517869976683259, 847723465796799, 216604590930944, 866135116349440, 361944410226688]
private def l:Array Nat:=#[1, 1216, 1245184, 1275068416, 1305670057984]
private def u:Array Nat:=#[517869976683259, 153931628669952, 615727311618048, 243811334750208, 302365697638400]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(996:ZMod 1009):=
  det_packed_compact 1009 m l u w 996 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 2 0).eval₂ order15Reduce (7:ZMod 1009)=(996:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 2 0 7 m 996
    (by decide +kernel) determinant
end S7
namespace S8
private def m:Array Nat:=#[776255209210728, 168225279942847, 260585170336768, 678235665858560, 766564689248256]
private def l:Array Nat:=#[1, 1192, 1220608, 1249902592, 1279900254208]
private def u:Array Nat:=#[776255209210728, 667403558952960, 186917891080192, 339585884225536, 452998790643712]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(974:ZMod 1009):=
  det_packed_compact 1009 m l u w 974 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 2 0).eval₂ order15Reduce (8:ZMod 1009)=(974:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 2 0 8 m 974
    (by decide +kernel) determinant
end S8
namespace S9
private def m:Array Nat:=#[1026943860343765, 881808326481087, 344148168342528, 325409471201280, 664310107865088]
private def l:Array Nat:=#[1, 1846, 1890304, 1935671296, 1982127407104]
private def u:Array Nat:=#[1026943860343765, 992859000886272, 737773330890752, 722332968550400, 195713069744128]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(880:ZMod 1009):=
  det_packed_compact 1009 m l u w 880 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 2 0).eval₂ order15Reduce (9:ZMod 1009)=(880:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 2 0 9 m 880
    (by decide +kernel) determinant
end S9
namespace S10
private def m:Array Nat:=#[81363860455505, 223200860521663, 234196061846528, 963259359297536, 271784456749056]
private def l:Array Nat:=#[1, 1562, 1599488, 1637875712, 1677184729088]
private def u:Array Nat:=#[81363860455505, 825733232542720, 862017201111040, 930273810186240, 173722837188608]
private def w:List (Fin 5×Fin 5):=[]
private theorem determinant:(rowMatrix 1009 5 m).det=(483:ZMod 1009):=
  det_packed_compact 1009 m l u w 483 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem verified:(nodeMomentNorm 5 1 2 0).eval₂ order15Reduce (10:ZMod 1009)=(483:ZMod 1009):=
  nodeMomentNorm_eval_from_rows (singleAxes 5) (by decide) 2 0 10 m 483
    (by decide +kernel) determinant
end S10
def candidate:List Nat:=[101, 628, 693, 294, 588, 523, 1001, 671, 643, 438, 415]
private def values:Fin 11→Nat:=fun i=>(#[101, 950, 518, 893, 554, 32, 85, 996, 974, 880, 483]:Array Nat)[i.val]!
theorem exactReduction:(nodeMomentNorm 5 1 2 0).map order15Reduce=residuePoly candidate:=by
  apply integer_reduction_of_residue_samples _ _ (d:=10) (by decide)
    ((nodeMomentNorm_degree (by decide) (by decide) 2 0).trans (by decide)) (by decide) values
  · intro i
    rw [eval_map]
    fin_cases i
    · exact S0.verified
    · exact S1.verified
    · exact S2.verified
    · exact S3.verified
    · exact S4.verified
    · exact S5.verified
    · exact S6.verified
    · exact S7.verified
    · exact S8.verified
    · exact S9.verified
    · exact S10.verified
  · decide +kernel
end J2

private def a : List Nat := [346, 926, 770, 112, 738, 149, 526, 496, 212, 497]
private def b : List Nat := [851, 399, 775, 118, 889, 504, 283, 434, 717, 206]

theorem one_checked_pair :
    Order15GoodPrimePair (nodeMomentNorm 5 1 1 0) (nodeMomentNorm 5 1 2 0)
      (momentCap 5 1 0) (momentCap 5 1 0) :=
  goodPrimePair_of_samples J1.candidate J2.candidate a b
    J1.exactReduction J2.exactReduction (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

end RKCert.FixedPolynomial.Order15Smoke
