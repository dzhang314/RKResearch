module
public import RKCert.Dirk15Replay.Axes

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N6K1J1W0
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
theorem checked : (nodeMomentNorm 6 1 1 0).eval₂ order15Reduce (0:ZMod 1009)=(452:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 0 (by decide) 0 m coefficients 452
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At0

namespace At1
private def m : Array Nat := #[308496574474879794, 969399819792337687, 770115537138899968, 327637752041439232, 554843004007874560, 137103602425528320]
private def l : Array Nat := #[1, 1527, 1563648, 1601175552, 1639603765248, 1678954255613952]
private def u : Array Nat := #[308496574474879794, 296111675500447744, 646266547385401344, 161004564999307264, 228331181693730816, 477381560501272576]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(714:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 714 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[1001, 240, 827, 728, 1002, 881, 334]
theorem checked : (nodeMomentNorm 6 1 1 0).eval₂ order15Reduce (1:ZMod 1009)=(714:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 0 (by decide) 1 m coefficients 714
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At1

namespace At2
private def m : Array Nat := #[128352589380059763, 33776997205921559, 1090997010388769792, 45036670339252224, 380118511726362624, 1053586126595424256]
private def l : Array Nat := #[1, 1780, 1822720, 1866465280, 1911260446720, 1957130697441280]
private def u : Array Nat := #[128352589380059763, 698057942243068928, 478507461065572352, 687925516316966912, 612053043206160384, 91197892454252544]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(919:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 919 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[306, 824, 583, 426, 108, 876, 442]
theorem checked : (nodeMomentNorm 6 1 1 0).eval₂ order15Reduce (2:ZMod 1009)=(919:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 0 (by decide) 2 m coefficients 919
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At2

namespace At3
private def m : Array Nat := #[155374187144282548, 583216151744926487, 75435294216444928, 1057220481506082816, 873052664202526720, 571700966466781184]
private def l : Array Nat := #[1, 1528, 1564672, 1602224128, 1640677507072, 1680053767241728]
private def u : Array Nat := #[155374187144282548, 660903245317066752, 973903419876048896, 976155687383990272, 793112921486917632, 967148019977814016]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(635:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 635 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[158, 169, 764, 768, 434, 31, 187]
theorem checked : (nodeMomentNorm 6 1 1 0).eval₂ order15Reduce (3:ZMod 1009)=(635:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 0 (by decide) 3 m coefficients 635
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At3

namespace At4
private def m : Array Nat := #[229683580995895541, 14636698789205783, 931119223216561152, 82190957095682048, 765882166331572224, 403941880347230208]
private def l : Array Nat := #[1, 1402, 1435648, 1470103552, 1505386037248, 1541515302141952]
private def u : Array Nat := #[229683580995895541, 668784544664769536, 329888672961789952, 347903334281117696, 1038349094457704448, 1076360310941548544]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(427:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 427 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[760, 88, 786, 727, 179, 556, 351]
theorem checked : (nodeMomentNorm 6 1 1 0).eval₂ order15Reduce (4:ZMod 1009)=(427:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 0 (by decide) 4 m coefficients 427
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At4

namespace At5
private def m : Array Nat := #[743093938516131894, 919860223890479895, 1066227211837398016, 211669241297895424, 478567683365797888, 825028445506371584]
private def l : Array Nat := #[1, 1730, 1771520, 1814036480, 1857573355520, 1902155116052480]
private def u : Array Nat := #[743093938516131894, 6755399441111040, 841047230468063232, 577586710192324608, 538239529098674176, 303992974847508480]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(847:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 847 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[975, 175, 46, 186, 238, 330, 363]
theorem checked : (nodeMomentNorm 6 1 1 0).eval₂ order15Reduce (5:ZMod 1009)=(847:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 0 (by decide) 5 m coefficients 847
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At5

namespace At6
private def m : Array Nat := #[570831252769211240, 691302542802264855, 1127025807664634880, 730709976673157120, 890420549874876416, 611107463206273024]
private def l : Array Nat := #[1, 1276, 1306624, 1337982976, 1370094567424, 1402976837042176]
private def u : Array Nat := #[570831252769211240, 1118018607495618560, 1122522208036454400, 727332276123205632, 504236032498073600, 1020065315599417344]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(567:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 567 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[405, 586, 722, 202, 846, 263, 444]
theorem checked : (nodeMomentNorm 6 1 1 0).eval₂ order15Reduce (6:ZMod 1009)=(567:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 0 (by decide) 6 m coefficients 567
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At6

namespace At7
private def m : Array Nat := #[713820540938224297, 755478837492098839, 426716065408244736, 483011792083091456, 671785961226502144, 260952592178216960]
private def l : Array Nat := #[1, 1240, 1269760, 1300234240, 1331439861760, 1363394418442240]
private def u : Array Nat := #[713820540938224297, 1070730811408032768, 899594026281336832, 432346295445749760, 439849731087138816, 841047230411440128]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(524:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 524 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[799, 739, 858, 886, 697, 432, 431]
theorem checked : (nodeMomentNorm 6 1 1 0).eval₂ order15Reduce (7:ZMod 1009)=(524:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 0 (by decide) 7 m coefficients 524
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At7

namespace At8
private def m : Array Nat := #[19140298416325098, 217298682021128983, 350154871542668288, 13511325845028864, 144654798103248896, 60542408760229888]
private def l : Array Nat := #[1, 1213, 1242112, 1271922688, 1302448832512, 1333707604492288]
private def u : Array Nat := #[19140298416325098, 7881299348400128, 1132655306797481984, 651896572195373056, 763898897536909312, 60798594969501696]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(109:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 109 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[736, 996, 941, 935, 556, 126, 325]
theorem checked : (nodeMomentNorm 6 1 1 0).eval₂ order15Reduce (8:ZMod 1009)=(109:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 0 (by decide) 8 m coefficients 109
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At8

namespace At9
private def m : Array Nat := #[19140298416324907, 43910096367169303, 966022120385305600, 216173103992012800, 289685879365042176, 456859175968833536]
private def l : Array Nat := #[1, 1192, 1220608, 1249902592, 1279900254208, 1310617860308992]
private def u : Array Nat := #[19140298416324907, 236438980437257216, 1005428617123987456, 573083373631700992, 574537706466443264, 551690954352885760]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(437:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 437 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[736, 264, 763, 834, 265, 791, 545]
theorem checked : (nodeMomentNorm 6 1 1 0).eval₂ order15Reduce (9:ZMod 1009)=(437:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 0 (by decide) 9 m coefficients 437
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At9

namespace At10
private def m : Array Nat := #[712694641031381100, 747597538143613719, 1070730811521391616, 895090542733426688, 324378769756258304, 846420543736381440]
private def l : Array Nat := #[1, 1377, 1410048, 1443889152, 1478542491648, 1514027511447552]
private def u : Array Nat := #[712694641031381100, 229683580996005888, 650770146268282880, 651896162025996288, 819773879437230080, 59672695062659072]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(395:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 395 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[637, 614, 694, 647, 242, 776, 879]
theorem checked : (nodeMomentNorm 6 1 1 0).eval₂ order15Reduce (10:ZMod 1009)=(395:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 0 (by decide) 10 m coefficients 395
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At10

namespace At11
private def m : Array Nat := #[920986123797267358, 383931868234283799, 528047057280982016, 374925664092946432, 663048142320566272, 836287444574797824]
private def l : Array Nat := #[1, 1987, 2034688, 2083520512, 2133525004288, 2184729604390912]
private def u : Array Nat := #[920986123797267358, 716072340752857088, 522417557745958912, 549440148824129536, 944522269701439488, 1067353111686807552]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(108:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 108 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[337, 756, 303, 469, 410, 42, 150]
theorem checked : (nodeMomentNorm 6 1 1 0).eval₂ order15Reduce (11:ZMod 1009)=(108:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 0 (by decide) 11 m coefficients 108
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At11

namespace At12
private def m : Array Nat := #[945755921747804895, 817403332368498455, 360287970961153024, 704814131713146880, 1028755605323513856, 83060406897082368]
private def l : Array Nat := #[1, 1150, 1177600, 1205862400, 1234803097600, 1264438371942400]
private def u : Array Nat := #[945755921747804895, 935622822586973184, 619244949534146560, 1066228000980205568, 736020780214648832, 600104650347118592]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(965:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 965 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[874, 568, 381, 512, 592, 708, 633]
theorem checked : (nodeMomentNorm 6 1 1 0).eval₂ order15Reduce (12:ZMod 1009)=(965:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 1 0 (by decide) 12 m coefficients 965
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At12


def candidate : List Nat := [452, 741, 558, 443, 537, 973, 758, 700, 60, 658, 364, 527, 1006]
private def values : Fin 13 → Nat := fun i => (#[452, 714, 919, 635, 427, 847, 567, 524, 109, 437, 395, 108, 965] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 6 1 1 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=12)
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
  · decide +kernel

end

end RKCert.FixedPolynomial.FixedReplay.N6K1J1W0
