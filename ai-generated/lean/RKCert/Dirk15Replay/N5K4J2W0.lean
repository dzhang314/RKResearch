module
public import RKCert.Dirk15Replay.Axes

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N5K4J2W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000
noncomputable section

namespace At0
private def m : Array Nat := #[439296, 449839104, 460635242496, 471690488315904, 690615531428658]
private def l : Array Nat := #[1, 1024, 1048576, 1073741824, 1099511627776]
private def u : Array Nat := #[690615531428658, 439296, 449839104, 460635242496, 471690488315904]
private def swaps : List (Fin 5×Fin 5) := [(3, 4), (2, 4), (1, 4), (0, 4)]
private theorem evaluated : (rowMatrix 1009 5 m).det=(577:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 577 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[320, 245, 793, 677, 332, 1001]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (0:ZMod 1009)=(577:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 0 m coefficients 577
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At0

namespace At1
private def m : Array Nat := #[859935650135823, 743527122797144, 180436091399457, 500074933989252, 781284860656434]
private def l : Array Nat := #[1, 1191, 1575317, 1772476147, 2166869528227]
private def u : Array Nat := #[859935650135823, 267394640946176, 543691964940288, 451538501763072, 703687441776640]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(303:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 303 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[341, 904, 700, 93, 292, 8]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (1:ZMod 1009)=(303:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 1 m coefficients 303
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At1

namespace At2
private def m : Array Nat := #[396481522043300, 872825287232252, 149212857026707, 1011181546507031, 975583863822130]
private def l : Array Nat := #[1, 1612, 1283930, 1241379541, 1741142805342]
private def u : Array Nat := #[396481522043300, 1103022417090560, 411863045111808, 674074716012544, 82463372083200]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(803:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 803 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[328, 860, 571, 612, 17, 161]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (2:ZMod 1009)=(803:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 2 m coefficients 803
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At2

namespace At3
private def m : Array Nat := #[865934418875233, 985261163987000, 1069649409246791, 635271457140394, 148962296753970]
private def l : Array Nat := #[1, 1416, 2006061, 1560805090, 1170169576105]
private def u : Array Nat := #[865934418875233, 150972352531456, 1011838826315776, 546136230199296, 613527488299008]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(962:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 962 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[969, 294, 670, 162, 541, 518]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (3:ZMod 1009)=(962:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 3 m coefficients 962
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At3

namespace At4
private def m : Array Nat := #[382132723112602, 884304246346810, 1300866992716, 370397280453181, 560629881550642]
private def l : Array Nat := #[1, 1318, 1210063, 1974535637, 1657804022964]
private def u : Array Nat := #[382132723112602, 764271761148928, 656528107372544, 23583665422336, 837827860365312]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(711:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 711 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[928, 39, 584, 470, 607, 525]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (4:ZMod 1009)=(711:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 4 m coefficients 711
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At4

namespace At5
private def m : Array Nat := #[943044390736906, 351110726136142, 744410621103266, 1059643355664848, 192147920738098]
private def l : Array Nat := #[1, 1461, 2006234, 1239541186, 1883038003065]
private def u : Array Nat := #[943044390736906, 164733041343488, 487586533474304, 562633199583232, 445302209249280]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(521:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 521 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[930, 600, 58, 434, 729, 611]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (5:ZMod 1009)=(521:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 5 m coefficients 521
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At5

namespace At6
private def m : Array Nat := #[727220262887123, 742320471646656, 539550119332154, 866437937605987, 873048116092722]
private def l : Array Nat := #[1, 1220, 1607424, 2116118353, 2117188402660]
private def u : Array Nat := #[727220262887123, 298082579723264, 1096581515313152, 571761078829056, 703687441776640]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(169:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 169 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[783, 165, 839, 594, 191, 765]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (6:ZMod 1009)=(169:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 6 m coefficients 169
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At6

namespace At7
private def m : Array Nat := #[493308609065176, 137909537263565, 332842152415267, 518078091586806, 1060621367550770]
private def l : Array Nat := #[1, 1192, 2011309, 1934298982, 1865015500331]
private def u : Array Nat := #[493308609065176, 590110969836544, 157020007170048, 233911435132928, 122045790683136]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(194:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 194 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[436, 688, 448, 540, 100, 122]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (7:ZMod 1009)=(194:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 7 m coefficients 194
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At7

namespace At8
private def m : Array Nat := #[972063454746166, 298812066348496, 890166267417934, 776649164841097, 571382014731058]
private def l : Array Nat := #[1, 1171, 1072560, 2074041781, 1411663731456]
private def u : Array Nat := #[972063454746166, 533202093975552, 319823149006848, 448608260325376, 575044581326848]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(97:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 97 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[28, 855, 78, 356, 385, 585]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (8:ZMod 1009)=(97:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 8 m coefficients 97
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At8

namespace At9
private def m : Array Nat := #[658726478125500, 430367166511607, 280133371322570, 1027902358816796, 753567758964530]
private def l : Array Nat := #[1, 1491, 1196037, 1108805308, 2105560417550]
private def u : Array Nat := #[658726478125500, 166579331289088, 814448217423872, 1076122309623808, 278176441827328]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(797:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 797 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[946, 149, 384, 46, 832, 357]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (9:ZMod 1009)=(797:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 9 m coefficients 797
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At9

namespace At10
private def m : Array Nat := #[367216286319776, 444613658770062, 499267595189896, 81653815856032, 520970807536434]
private def l : Array Nat := #[1, 1747, 1262127, 2114144045, 1856643674609]
private def u : Array Nat := #[367216286319776, 876253538922496, 968536617910272, 783435320786944, 80264348827648]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(746:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 746 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[829, 897, 300, 978, 101, 590]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (10:ZMod 1009)=(746:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 10 m coefficients 746
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At10

namespace At11
private def m : Array Nat := #[180976291120782, 909056733711841, 1056656683199127, 309926046412595, 1019985248694066]
private def l : Array Nat := #[1, 1773, 1543655, 1103863623, 1716092190481]
private def u : Array Nat := #[180976291120782, 87118524195840, 1088191064965120, 324187352727552, 192414534860800]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(362:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 362 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[680, 227, 901, 265, 797, 935]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (11:ZMod 1009)=(362:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 11 m coefficients 362
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At11

namespace At12
private def m : Array Nat := #[262709530518997, 196521667150381, 580567231928567, 676075910210246, 557001766545202]
private def l : Array Nat := #[1, 1122, 1473728, 2114303965, 1435261439763]
private def u : Array Nat := #[262709530518997, 68144685148160, 161628212428800, 817029481234432, 1067625790570496]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(380:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 380 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[879, 187, 184, 281, 415, 137]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (12:ZMod 1009)=(380:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 12 m coefficients 380
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At12

namespace At13
private def m : Array Nat := #[633444976793372, 437181333962174, 918404550824345, 873571788997209, 1029115891477298]
private def l : Array Nat := #[1, 1813, 1266150, 1777160805, 1604983408588]
private def u : Array Nat := #[633444976793372, 1090859690615808, 1066270661279744, 847752456044544, 520068999938048]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(795:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 795 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[223, 711, 966, 15, 447, 666]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (13:ZMod 1009)=(795:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 13 m coefficients 795
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At13

namespace At14
private def m : Array Nat := #[954435400203693, 584062481994449, 404124962058380, 1018571479508460, 26356210089778]
private def l : Array Nat := #[1, 1108, 1508128, 1546340713, 1902282997086]
private def u : Array Nat := #[954435400203693, 294247861747712, 675949415759872, 527603446317056, 58274116272128]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(632:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 632 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[11, 657, 620, 551, 354, 231]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (14:ZMod 1009)=(632:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 14 m coefficients 632
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At14

namespace At15
private def m : Array Nat := #[489552955534122, 405276991142834, 706568606323137, 233237642149247, 851109241250610]
private def l : Array Nat := #[1, 1506, 1352489, 1549835617, 2119320093844]
private def u : Array Nat := #[489552955534122, 874873060952064, 689816614207488, 753254585597952, 766359604559872]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(364:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 364 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[57, 863, 991, 458, 619, 447]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (15:ZMod 1009)=(364:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 15 m coefficients 364
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At15

namespace At16
private def m : Array Nat := #[1020657133532120, 367449799488173, 630763103414599, 779767785613586, 772659785312050]
private def l : Array Nat := #[1, 1602, 1213548, 1776269745, 1837567148080]
private def u : Array Nat := #[1020657133532120, 812137632466944, 532201937567744, 832208969400320, 829031767343104]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(651:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 651 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[757, 140, 150, 261, 755, 367]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (16:ZMod 1009)=(651:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 16 m coefficients 651
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At16

namespace At17
private def m : Array Nat := #[239579207009906, 153536495436287, 168666751369999, 1096651319127205, 1007593615380274]
private def l : Array Nat := #[1, 1568, 1920567, 1416665625, 1299757372730]
private def u : Array Nat := #[239579207009906, 158602426846208, 843179645468672, 918109389062144, 434307092971520]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(494:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 494 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[111, 346, 292, 858, 340, 104]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (17:ZMod 1009)=(494:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 17 m coefficients 494
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At17

namespace At18
private def m : Array Nat := #[78001242401833, 734752393454565, 381408867929896, 1040143251190840, 741464227156786]
private def l : Array Nat := #[1, 1762, 1729270, 1801898576, 1238218962063]
private def u : Array Nat := #[78001242401833, 513657446674432, 482147694542848, 817695201165312, 690493302243328]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(945:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 945 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[835, 361, 499, 928, 52, 417]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (18:ZMod 1009)=(945:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 18 m coefficients 945
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At18

namespace At19
private def m : Array Nat := #[408290413911204, 547142596590266, 212649589271954, 472762135283644, 239700821619506]
private def l : Array Nat := #[1, 1139, 2035318, 1904668589, 1816416117024]
private def u : Array Nat := #[408290413911204, 231111140807680, 133524981022720, 278951683424256, 15393162788864]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(493:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 493 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[320, 152, 602, 393, 686, 279]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (19:ZMod 1009)=(493:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 19 m coefficients 493
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At19

namespace At20
private def m : Array Nat := #[989512781616670, 673953029480635, 236182325099070, 58950017278799, 896222185215794]
private def l : Array Nat := #[1, 1890, 1926536, 1429457376, 1583247769553]
private def u : Array Nat := #[989512781616670, 19470608545792, 564797027385344, 1052417311375360, 472789999943680]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(861:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 861 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[771, 802, 1007, 853, 153, 499]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (20:ZMod 1009)=(861:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 20 m coefficients 861
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At20

namespace At21
private def m : Array Nat := #[463098841618775, 703634831204389, 1108259779545403, 969161006688994, 263593722626866]
private def l : Array Nat := #[1, 1080, 1773348, 1115365169, 1290036564797]
private def u : Array Nat := #[463098841618775, 297325506088960, 384572861710336, 263634756304896, 517869976682496]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(249:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 249 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[175, 503, 503, 976, 569, 281]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (21:ZMod 1009)=(249:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 21 m coefficients 249
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At21

namespace At22
private def m : Array Nat := #[412557859073398, 179825638130485, 78901108850298, 129839126583925, 143569859837746]
private def l : Array Nat := #[1, 1903, 2005366, 2096995559, 1830700465123]
private def u : Array Nat := #[412557859073398, 529318947889152, 914913633501184, 95943126941696, 826832744087552]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(10:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 10 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[422, 639, 124, 969, 209, 846]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (22:ZMod 1009)=(10:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 22 m coefficients 10
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At22

namespace At23
private def m : Array Nat := #[571384444337206, 607597407598677, 1076515409633802, 1015827595645448, 160886811413298]
private def l : Array Nat := #[1, 1119, 1545562, 1983204399, 1309933174986]
private def u : Array Nat := #[571384444337206, 757475312435200, 326761960177664, 428543246860288, 422212465065984]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(854:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 854 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[291, 770, 957, 995, 596, 982]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (23:ZMod 1009)=(854:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 23 m coefficients 854
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At23

namespace At24
private def m : Array Nat := #[490427724086713, 752848545718692, 654690155043804, 25754837936539, 996363780028210]
private def l : Array Nat := #[1, 1073, 1232944, 1827039734, 1686133451621]
private def u : Array Nat := #[490427724086713, 21629944564736, 1091484989259776, 560158224678912, 1006053139415040]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(512:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 512 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[544, 679, 941, 599, 473, 666]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (24:ZMod 1009)=(512:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 24 m coefficients 512
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At24

namespace At25
private def m : Array Nat := #[1072820815121604, 170618517703037, 824103661794318, 607762350781742, 953508126764850]
private def l : Array Nat := #[1, 1515, 1863593, 1651092065, 1155822809782]
private def u : Array Nat := #[1072820815121604, 775271351750656, 932566798434304, 28362890280960, 104453604638720]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(992:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 992 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[948, 401, 747, 152, 874, 650]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (25:ZMod 1009)=(992:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 25 m coefficients 992
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At25

namespace At26
private def m : Array Nat := #[799584120461940, 373145704585757, 1081325521257075, 741627338343617, 899952945835826]
private def l : Array Nat := #[1, 1923, 2041458, 1307556295, 1676124729657]
private def u : Array Nat := #[799584120461940, 658139047758848, 708090323271680, 1019539336724480, 693791837126656]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(346:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 346 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[324, 252, 577, 277, 105, 29]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (26:ZMod 1009)=(346:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 26 m coefficients 346
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At26

namespace At27
private def m : Array Nat := #[701668897940105, 807783388470736, 682710917040937, 405620206124116, 562246060369714]
private def l : Array Nat := #[1, 1516, 1366465, 1846793653, 1838376608420]
private def u : Array Nat := #[701668897940105, 701218876025856, 1109381508759552, 114655225708544, 760862046420992]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(884:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 884 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[632, 858, 999, 266, 833, 872]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (27:ZMod 1009)=(884:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 27 m coefficients 884
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At27

namespace At28
private def m : Array Nat := #[209597531040554, 150540813388499, 72600108255792, 155928152269784, 120207681725234]
private def l : Array Nat := #[1, 1066, 1062088, 1119977376, 1947024800916]
private def u : Array Nat := #[209597531040554, 250912180850688, 517973735374848, 429454853668864, 1017048255692800]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(9:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 9 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[966, 157, 755, 533, 22, 745]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (28:ZMod 1009)=(9:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 28 m coefficients 9
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At28

namespace At29
private def m : Array Nat := #[781601700700434, 83252406122354, 370466565334905, 825311814805355, 755866617732914]
private def l : Array Nat := #[1, 1830, 1559964, 1262726335, 2175465412692]
private def u : Array Nat := #[781601700700434, 1019656620627968, 1082977649950720, 999479691968512, 207807697649664]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(869:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 869 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[630, 491, 623, 22, 58, 369]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (29:ZMod 1009)=(869:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 29 m coefficients 869
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At29

namespace At30
private def m : Array Nat := #[107858186855252, 972692999420409, 884534689408787, 996316410710782, 635357272948530]
private def l : Array Nat := #[1, 1265, 1477567, 1874046879, 1563558555390]
private def u : Array Nat := #[107858186855252, 520351586284544, 779975793836032, 618653531766784, 215504279044096]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(384:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 384 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[196, 563, 216, 678, 703, 179]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (30:ZMod 1009)=(384:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 30 m coefficients 384
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At30

namespace At31
private def m : Array Nat := #[1064739710489525, 1047368020621477, 244406467217662, 25898468965009, 923469134961458]
private def l : Array Nat := #[1, 1778, 1654193, 2004788768, 1511155917844]
private def u : Array Nat := #[1064739710489525, 646096856150016, 1101670947749888, 53050362298368, 901599534776320]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(991:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 991 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[544, 511, 835, 819, 130, 919]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (31:ZMod 1009)=(991:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 31 m coefficients 991
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At31

namespace At32
private def m : Array Nat := #[1099004575699553, 693794021196211, 1109337910465835, 1063951420683812, 340603730738]
private def l : Array Nat := #[1, 1313, 1612827, 1486416809, 1251775409155]
private def u : Array Nat := #[1099004575699553, 543357436528640, 555449497681920, 534999380000768, 909296116170752]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(994:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 994 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[893, 928, 250, 616, 1003, 201]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (32:ZMod 1009)=(994:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 32 m coefficients 994
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At32

namespace At33
private def m : Array Nat := #[185407153120762, 175826616126319, 725513354715034, 767225572362679, 603293337358130]
private def l : Array Nat := #[1, 1610, 1348535, 1204673141, 1433852346577]
private def u : Array Nat := #[185407153120762, 652716451525632, 775780032315392, 677169239949312, 57174604644352]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(109:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 109 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[868, 873, 598, 510, 413, 163]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (33:ZMod 1009)=(109:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 33 m coefficients 109
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At33

namespace At34
private def m : Array Nat := #[325842145397671, 145230185504820, 615596894148713, 85185158843722, 5273525938994]
private def l : Array Nat := #[1, 1296, 1181066, 1948823478, 2084519732622]
private def u : Array Nat := #[325842145397671, 373879019176960, 556437734424576, 142575734358016, 368336395304960]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(525:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 525 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[549, 927, 137, 638, 1003, 1001]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (34:ZMod 1009)=(525:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 34 m coefficients 525
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At34

namespace At35
private def m : Array Nat := #[968236704235299, 1045394946941473, 993785648325483, 628297400883421, 583966581772082]
private def l : Array Nat := #[1, 1663, 1682560, 1802930748, 1720049737278]
private def u : Array Nat := #[968236704235299, 707144717184000, 879633650155520, 309949536141312, 1053332139409408]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(218:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 218 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[520, 195, 135, 259, 904, 555]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (35:ZMod 1009)=(218:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 35 m coefficients 218
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At35

namespace At36
private def m : Array Nat := #[571710310479504, 758131337711505, 999167548124365, 1031382075882608, 896484201794354]
private def l : Array Nat := #[1, 1393, 1955510, 1321872458, 1692908219464]
private def u : Array Nat := #[571710310479504, 976877475213312, 63012973051904, 668690974507008, 926888302215168]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(146:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 146 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[909, 371, 660, 207, 824, 958]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (36:ZMod 1009)=(146:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 36 m coefficients 146
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At36

namespace At37
private def m : Array Nat := #[457087734702741, 1035089586839248, 303270461198449, 1088981077512195, 839495473305394]
private def l : Array Nat := #[1, 1683, 1775476, 1794400717, 2047465656567]
private def u : Array Nat := #[457087734702741, 984839967077376, 877372251308032, 392317345202176, 479387069710336]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(544:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 544 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[428, 722, 406, 299, 38, 150]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (37:ZMod 1009)=(544:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 37 m coefficients 544
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At37

namespace At38
private def m : Array Nat := #[733118936715870, 993663179999771, 982389363808855, 336111416960903, 162956805318450]
private def l : Array Nat := #[1, 1586, 1386134, 1255380464, 1327027868690]
private def u : Array Nat := #[733118936715870, 1045565143297024, 181878457892864, 15036680503296, 101155069755392]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(506:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 506 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[458, 135, 555, 779, 450, 545]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (38:ZMod 1009)=(506:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 38 m coefficients 506
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At38

namespace At39
private def m : Array Nat := #[592262545709965, 392048197690287, 784851952347790, 1073301068325658, 461619329825586]
private def l : Array Nat := #[1, 1287, 1817654, 1879781010, 1213947061260]
private def u : Array Nat := #[592262545709965, 134826123259904, 121858086141952, 1046348522586112, 248489627877376]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(54:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 54 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[53, 173, 567, 735, 565, 545]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (39:ZMod 1009)=(54:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 39 m coefficients 54
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At39

namespace At40
private def m : Array Nat := #[74113200049752, 985939608064487, 1078852646945046, 297456903818925, 416566634300210]
private def l : Array Nat := #[1, 1457, 2058338, 1314207804, 1947687750639]
private def u : Array Nat := #[74113200049752, 151310394243072, 652300008816640, 386221712867328, 646512837132288]
private def swaps : List (Fin 5×Fin 5) := []
private theorem evaluated : (rowMatrix 1009 5 m).det=(127:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 127 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[25, 59, 24, 552, 560, 180]
theorem checked : (nodeMomentNorm 5 4 2 0).eval₂ order15Reduce (40:ZMod 1009)=(127:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes5K4 2 0 (by decide) 40 m coefficients 127
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At40


def candidate : List Nat := [577, 964, 43, 606, 360, 955, 954, 913, 454, 629, 82, 713, 227, 889, 743, 257, 320, 552, 395, 529, 628, 400, 774, 293, 132, 678, 563, 619, 581, 703, 219, 450, 801, 156, 555, 445, 554, 358, 926, 47, 448]
private def values : Fin 41 → Nat := fun i => (#[577, 303, 803, 962, 711, 521, 169, 194, 97, 797, 746, 362, 380, 795, 632, 364, 651, 494, 945, 493, 861, 249, 10, 854, 512, 992, 346, 884, 9, 869, 384, 991, 994, 109, 525, 218, 146, 544, 506, 54, 127] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 5 4 2 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=40)
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

end RKCert.FixedPolynomial.FixedReplay.N5K4J2W0
