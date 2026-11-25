module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripRowCheck
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate
open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

def packet0576 : StripRowPacket :=
  ⟨⟨⟨7,22,5,8⟩,
    ![349,1217,2500,4007,5523,6838,7770],![380,1264,2547,4045,5549,6853,7777]⟩,
    ⟨-619250176814200200130867903,98953273037681957037136414720⟩,
    ⟨-327596485389001580634549197,61209755247246786715731722240⟩⟩

def packet0577 : StripRowPacket :=
  ⟨⟨⟨7,22,5,9⟩,
    ![373,1254,2536,4035,5542,6847,7773],![400,1300,2584,4075,5569,6863,7780]⟩,
    ⟨-9584713908834635153895085705,1741577605463202443853600899072⟩,
    ⟨-140699830731270707096441401,30604877623623393357865861120⟩⟩

def packet0578 : StripRowPacket :=
  ⟨⟨⟨7,23,4,4⟩,
    ![348,1214,2496,4004,5521,6836,7770],![398,1296,2579,4071,5567,6862,7780]⟩,
    ⟨-86465310324184922758093,13659859742417732783779840⟩,
    ⟨-274178811733541710870671,58934667582777754362383360⟩⟩

def packet0579 : StripRowPacket :=
  ⟨⟨⟨7,22,4,5⟩,
    ![392,1289,2572,4065,5561,6857,7776],![432,1364,2657,4139,5614,6887,7788]⟩,
    ⟨-20676561764348366963717240793,4353944013658006109634002247680⟩,
    ⟨-47251503402405270327387503,15302438811811696678932930560⟩⟩

def packet0580 : StripRowPacket :=
  ⟨⟨⟨7,23,4,5⟩,
    ![391,1285,2568,4061,5559,6856,7776],![430,1360,2653,4136,5612,6886,7788]⟩,
    ⟨-52473855994234213841101,10927887793934186227023872⟩,
    ⟨-18410221216636105071145,5893466758277775436238336⟩⟩

def packet0581 : StripRowPacket :=
  ⟨⟨⟨6,10,4,6⟩,
    ![425,1354,2646,4128,5606,6881,7784],![462,1432,2742,4218,5672,6919,7798]⟩,
    ⟨-2444706522795642531809,748556213860793143629824⟩,
    ⟨-6594151748063705081764843,4471960371468889458688122880⟩⟩

def packet0582 : StripRowPacket :=
  ⟨⟨⟨6,10,4,7⟩,
    ![450,1410,2717,4195,5655,6908,7793],![482,1480,2812,4291,5730,6953,7810]⟩,
    ⟨-1910007380998672350359,1069366019801133062328320⟩,
    ⟨3385216765375971359331,558995046433611182336015360⟩⟩

def packet0583 : StripRowPacket :=
  ⟨⟨⟨6,11,4,6⟩,
    ![422,1347,2638,4122,5601,6879,7783],![457,1423,2733,4211,5667,6917,7798]⟩,
    ⟨-1022716800708499901337,306918883663174998691840⟩,
    ⟨-154728755606037994973,102387915240565380208640⟩⟩

def packet0584 : StripRowPacket :=
  ⟨⟨⟨6,11,4,7⟩,
    ![446,1403,2710,4189,5650,6906,7792],![476,1471,2802,4283,5725,6951,7809]⟩,
    ⟨-12247780301241379653463,6752215440589849971220480⟩,
    ⟨100537058408689673,12798489405070672526080⟩⟩

def packet0585 : StripRowPacket :=
  ⟨⟨⟨6,12,4,0⟩,
    ![0,918,2252,3823,5405,6778,7752],![143,1000,2314,3870,5436,6795,7759]⟩,
    ⟨-213263953635397,16749981306508736⟩,
    ⟨-97166580075128527842631,8926124595461024915611648⟩⟩

def packet0586 : StripRowPacket :=
  ⟨⟨⟨6,12,4,1⟩,
    ![102,980,2301,3858,5428,6789,7755],![235,1072,2371,3911,5462,6808,7763]⟩,
    ⟨-24237646234895570572423,2168643395727664710080512⟩,
    ⟨-5948105040988538841025,637580328247216065400832⟩⟩

def packet0587 : StripRowPacket :=
  ⟨⟨⟨6,13,4,0⟩,
    ![0,912,2244,3816,5400,6775,7751],![142,994,2306,3862,5431,6792,7758]⟩,
    ⟨-1890561502183,145253328494560⟩,
    ⟨-3090344683816330247284261,277427871422013214408929280⟩⟩

def packet0588 : StripRowPacket :=
  ⟨⟨⟨6,13,4,1⟩,
    ![103,974,2293,3851,5423,6786,7754],![233,1066,2363,3904,5457,6805,7762]⟩,
    ⟨-20980737547186124653983959,1836659148089293225071435776⟩,
    ⟨-1324212422966566513902981,138713935711006607204464640⟩⟩

def packet0589 : StripRowPacket :=
  ⟨⟨⟨7,24,4,2⟩,
    ![213,1057,2361,3903,5456,6803,7760],![301,1146,2433,3957,5491,6823,7768]⟩,
    ⟨-12010608986284473629837,1265009901872872549281536⟩,
    ⟨-8330394131825747244369657,1067896561966680596896858112⟩⟩

def packet0590 : StripRowPacket :=
  ⟨⟨⟨7,25,4,2⟩,
    ![212,1054,2357,3899,5453,6802,7759],![300,1142,2429,3953,5489,6822,7767]⟩,
    ⟨-304117301596681280970918545607,31673281204650318004641059627008⟩,
    ⟨-253480267674867996615425340637,32121508226527571785025872519168⟩⟩

def packet0591 : StripRowPacket :=
  ⟨⟨⟨7,24,4,3⟩,
    ![289,1134,2424,3948,5485,6818,7764],![355,1221,2503,4009,5525,6840,7773]⟩,
    ⟨-261402152527897726672945,32890257448694686281319936⟩,
    ⟨-1669558843964321996942675,266974140491670149224214528⟩⟩

def packet0592 : StripRowPacket :=
  ⟨⟨⟨7,25,4,3⟩,
    ![288,1131,2420,3945,5482,6817,7764],![354,1218,2499,4006,5523,6839,7773]⟩,
    ⟨-509081653277305912022169448405,63346562409300636009282119254016⟩,
    ⟨-50797908739854208496987150575,8030377056631892946256468129792⟩⟩

def packet0593 : StripRowPacket :=
  ⟨⟨⟨6,13,4,2⟩,
    ![205,1045,2349,3892,5448,6799,7758],![302,1142,2427,3951,5487,6821,7767]⟩,
    ⟨-45140563647867336447796403,4591647870223233062678589440⟩,
    ⟨-2206505008049935808327663,277427871422013214408929280⟩⟩

def packet0594 : StripRowPacket :=
  ⟨⟨⟨7,26,4,3⟩,
    ![288,1128,2416,3942,5480,6815,7763],![353,1215,2495,4002,5521,6838,7772]⟩,
    ⟨-17069405564306657049980936973,2101051929533156885805327441920⟩,
    ⟨-115807429183552370573817233981,18103510422071499262454277140480⟩⟩

def packet0595 : StripRowPacket :=
  ⟨⟨⟨7,27,4,3⟩,
    ![287,1125,2413,3938,5478,6814,7763],![351,1212,2491,3999,5518,6836,7772]⟩,
    ⟨-2062496717642213839365464419,251185488329592775562605281280⟩,
    ⟨-355983313594044930240463,55042743462600368683985920⟩⟩

def packet0596 : StripRowPacket :=
  ⟨⟨⟨6,14,4,0⟩,
    ![0,906,2237,3809,5396,6773,7750],![140,988,2298,3855,5426,6790,7757]⟩,
    ⟨-273422529761103,20568925663951808⟩,
    ⟨-2080959364493817230113145,182747484171155989944590336⟩⟩

def packet0597 : StripRowPacket :=
  ⟨⟨⟨6,14,4,1⟩,
    ![103,969,2286,3845,5418,6784,7753],![231,1060,2355,3897,5452,6803,7761]⟩,
    ⟨-3974046532583093980562533,340680575098335784576675840⟩,
    ⟨-57958800434904491823936569,5939293235562569673199185920⟩⟩

def packet0598 : StripRowPacket :=
  ⟨⟨⟨6,15,4,0⟩,
    ![0,901,2229,3803,5391,6770,7749],![139,983,2291,3849,5421,6787,7757]⟩,
    ⟨-1146367,84510140⟩,
    ⟨-4841572842093608671,416315055438384593920⟩⟩

def packet0599 : StripRowPacket :=
  ⟨⟨⟨6,15,4,1⟩,
    ![103,964,2279,3838,5413,6781,7753],![230,1055,2348,3890,5448,6800,7761]⟩,
    ⟨-131609315277554837285,11057768009379424526336⟩,
    ⟨-2074536840911246311,208157527719192296960⟩⟩

def packets024 : List StripRowPacket :=
  [packet0576, packet0577, packet0578, packet0579, packet0580, packet0581,
   packet0582, packet0583, packet0584, packet0585, packet0586, packet0587,
   packet0588, packet0589, packet0590, packet0591, packet0592, packet0593,
   packet0594, packet0595, packet0596, packet0597, packet0598, packet0599]

theorem packet0576_membership : packet0576 ∈ packets024 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0576_shape : checkStripShape packet0576.row = true := by
  decide +kernel

private theorem packet0576_cache : checkStripCache packet0576 = true := by
  decide +kernel

private theorem packet0576_pair (i : Fin 7) : checkEdgePair packet0576 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0576_ok : checkStripPacket packet0576 = true :=
  checkStripPacket_intro packet0576_shape packet0576_cache packet0576_pair

theorem packet0577_membership : packet0577 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0577_shape : checkStripShape packet0577.row = true := by
  decide +kernel

private theorem packet0577_cache : checkStripCache packet0577 = true := by
  decide +kernel

private theorem packet0577_pair (i : Fin 7) : checkEdgePair packet0577 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0577_ok : checkStripPacket packet0577 = true :=
  checkStripPacket_intro packet0577_shape packet0577_cache packet0577_pair

theorem packet0578_membership : packet0578 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0578_shape : checkStripShape packet0578.row = true := by
  decide +kernel

private theorem packet0578_cache : checkStripCache packet0578 = true := by
  decide +kernel

private theorem packet0578_pair (i : Fin 7) : checkEdgePair packet0578 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0578_ok : checkStripPacket packet0578 = true :=
  checkStripPacket_intro packet0578_shape packet0578_cache packet0578_pair

theorem packet0579_membership : packet0579 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0579_shape : checkStripShape packet0579.row = true := by
  decide +kernel

private theorem packet0579_cache : checkStripCache packet0579 = true := by
  decide +kernel

private theorem packet0579_pair (i : Fin 7) : checkEdgePair packet0579 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0579_ok : checkStripPacket packet0579 = true :=
  checkStripPacket_intro packet0579_shape packet0579_cache packet0579_pair

theorem packet0580_membership : packet0580 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0580_shape : checkStripShape packet0580.row = true := by
  decide +kernel

private theorem packet0580_cache : checkStripCache packet0580 = true := by
  decide +kernel

private theorem packet0580_pair (i : Fin 7) : checkEdgePair packet0580 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0580_ok : checkStripPacket packet0580 = true :=
  checkStripPacket_intro packet0580_shape packet0580_cache packet0580_pair

theorem packet0581_membership : packet0581 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0581_shape : checkStripShape packet0581.row = true := by
  decide +kernel

private theorem packet0581_cache : checkStripCache packet0581 = true := by
  decide +kernel

private theorem packet0581_pair (i : Fin 7) : checkEdgePair packet0581 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0581_ok : checkStripPacket packet0581 = true :=
  checkStripPacket_intro packet0581_shape packet0581_cache packet0581_pair

theorem packet0582_membership : packet0582 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0582_shape : checkStripShape packet0582.row = true := by
  decide +kernel

private theorem packet0582_cache : checkStripCache packet0582 = true := by
  decide +kernel

private theorem packet0582_pair (i : Fin 7) : checkEdgePair packet0582 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0582_ok : checkStripPacket packet0582 = true :=
  checkStripPacket_intro packet0582_shape packet0582_cache packet0582_pair

theorem packet0583_membership : packet0583 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0583_shape : checkStripShape packet0583.row = true := by
  decide +kernel

private theorem packet0583_cache : checkStripCache packet0583 = true := by
  decide +kernel

private theorem packet0583_pair (i : Fin 7) : checkEdgePair packet0583 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0583_ok : checkStripPacket packet0583 = true :=
  checkStripPacket_intro packet0583_shape packet0583_cache packet0583_pair

theorem packet0584_membership : packet0584 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0584_shape : checkStripShape packet0584.row = true := by
  decide +kernel

private theorem packet0584_cache : checkStripCache packet0584 = true := by
  decide +kernel

private theorem packet0584_pair (i : Fin 7) : checkEdgePair packet0584 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0584_ok : checkStripPacket packet0584 = true :=
  checkStripPacket_intro packet0584_shape packet0584_cache packet0584_pair

theorem packet0585_membership : packet0585 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0585_shape : checkStripShape packet0585.row = true := by
  decide +kernel

private theorem packet0585_cache : checkStripCache packet0585 = true := by
  decide +kernel

private theorem packet0585_pair (i : Fin 7) : checkEdgePair packet0585 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0585_ok : checkStripPacket packet0585 = true :=
  checkStripPacket_intro packet0585_shape packet0585_cache packet0585_pair

theorem packet0586_membership : packet0586 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0586_shape : checkStripShape packet0586.row = true := by
  decide +kernel

private theorem packet0586_cache : checkStripCache packet0586 = true := by
  decide +kernel

private theorem packet0586_pair (i : Fin 7) : checkEdgePair packet0586 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0586_ok : checkStripPacket packet0586 = true :=
  checkStripPacket_intro packet0586_shape packet0586_cache packet0586_pair

theorem packet0587_membership : packet0587 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0587_shape : checkStripShape packet0587.row = true := by
  decide +kernel

private theorem packet0587_cache : checkStripCache packet0587 = true := by
  decide +kernel

private theorem packet0587_pair (i : Fin 7) : checkEdgePair packet0587 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0587_ok : checkStripPacket packet0587 = true :=
  checkStripPacket_intro packet0587_shape packet0587_cache packet0587_pair

theorem packet0588_membership : packet0588 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0588_shape : checkStripShape packet0588.row = true := by
  decide +kernel

private theorem packet0588_cache : checkStripCache packet0588 = true := by
  decide +kernel

private theorem packet0588_pair (i : Fin 7) : checkEdgePair packet0588 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0588_ok : checkStripPacket packet0588 = true :=
  checkStripPacket_intro packet0588_shape packet0588_cache packet0588_pair

theorem packet0589_membership : packet0589 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0589_shape : checkStripShape packet0589.row = true := by
  decide +kernel

private theorem packet0589_cache : checkStripCache packet0589 = true := by
  decide +kernel

private theorem packet0589_pair (i : Fin 7) : checkEdgePair packet0589 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0589_ok : checkStripPacket packet0589 = true :=
  checkStripPacket_intro packet0589_shape packet0589_cache packet0589_pair

theorem packet0590_membership : packet0590 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0590_shape : checkStripShape packet0590.row = true := by
  decide +kernel

private theorem packet0590_cache : checkStripCache packet0590 = true := by
  decide +kernel

private theorem packet0590_pair (i : Fin 7) : checkEdgePair packet0590 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0590_ok : checkStripPacket packet0590 = true :=
  checkStripPacket_intro packet0590_shape packet0590_cache packet0590_pair

theorem packet0591_membership : packet0591 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0591_shape : checkStripShape packet0591.row = true := by
  decide +kernel

private theorem packet0591_cache : checkStripCache packet0591 = true := by
  decide +kernel

private theorem packet0591_pair (i : Fin 7) : checkEdgePair packet0591 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0591_ok : checkStripPacket packet0591 = true :=
  checkStripPacket_intro packet0591_shape packet0591_cache packet0591_pair

theorem packet0592_membership : packet0592 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0592_shape : checkStripShape packet0592.row = true := by
  decide +kernel

private theorem packet0592_cache : checkStripCache packet0592 = true := by
  decide +kernel

private theorem packet0592_pair (i : Fin 7) : checkEdgePair packet0592 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0592_ok : checkStripPacket packet0592 = true :=
  checkStripPacket_intro packet0592_shape packet0592_cache packet0592_pair

theorem packet0593_membership : packet0593 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0593_shape : checkStripShape packet0593.row = true := by
  decide +kernel

private theorem packet0593_cache : checkStripCache packet0593 = true := by
  decide +kernel

private theorem packet0593_pair (i : Fin 7) : checkEdgePair packet0593 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0593_ok : checkStripPacket packet0593 = true :=
  checkStripPacket_intro packet0593_shape packet0593_cache packet0593_pair

theorem packet0594_membership : packet0594 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0594_shape : checkStripShape packet0594.row = true := by
  decide +kernel

private theorem packet0594_cache : checkStripCache packet0594 = true := by
  decide +kernel

private theorem packet0594_pair (i : Fin 7) : checkEdgePair packet0594 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0594_ok : checkStripPacket packet0594 = true :=
  checkStripPacket_intro packet0594_shape packet0594_cache packet0594_pair

theorem packet0595_membership : packet0595 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0595_shape : checkStripShape packet0595.row = true := by
  decide +kernel

private theorem packet0595_cache : checkStripCache packet0595 = true := by
  decide +kernel

private theorem packet0595_pair (i : Fin 7) : checkEdgePair packet0595 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0595_ok : checkStripPacket packet0595 = true :=
  checkStripPacket_intro packet0595_shape packet0595_cache packet0595_pair

theorem packet0596_membership : packet0596 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0596_shape : checkStripShape packet0596.row = true := by
  decide +kernel

private theorem packet0596_cache : checkStripCache packet0596 = true := by
  decide +kernel

private theorem packet0596_pair (i : Fin 7) : checkEdgePair packet0596 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0596_ok : checkStripPacket packet0596 = true :=
  checkStripPacket_intro packet0596_shape packet0596_cache packet0596_pair

theorem packet0597_membership : packet0597 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0597_shape : checkStripShape packet0597.row = true := by
  decide +kernel

private theorem packet0597_cache : checkStripCache packet0597 = true := by
  decide +kernel

private theorem packet0597_pair (i : Fin 7) : checkEdgePair packet0597 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0597_ok : checkStripPacket packet0597 = true :=
  checkStripPacket_intro packet0597_shape packet0597_cache packet0597_pair

theorem packet0598_membership : packet0598 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0598_shape : checkStripShape packet0598.row = true := by
  decide +kernel

private theorem packet0598_cache : checkStripCache packet0598 = true := by
  decide +kernel

private theorem packet0598_pair (i : Fin 7) : checkEdgePair packet0598 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0598_ok : checkStripPacket packet0598 = true :=
  checkStripPacket_intro packet0598_shape packet0598_cache packet0598_pair

theorem packet0599_membership : packet0599 ∈ packets024 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0599_shape : checkStripShape packet0599.row = true := by
  decide +kernel

private theorem packet0599_cache : checkStripCache packet0599 = true := by
  decide +kernel

private theorem packet0599_pair (i : Fin 7) : checkEdgePair packet0599 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0599_ok : checkStripPacket packet0599 = true :=
  checkStripPacket_intro packet0599_shape packet0599_cache packet0599_pair

theorem packets024_checked : packets024.all checkStripPacket = true := by
  simp only [packets024, List.all_cons, List.all_nil, Bool.true_and, packet0576_ok,
    packet0577_ok, packet0578_ok, packet0579_ok, packet0580_ok, packet0581_ok,
    packet0582_ok, packet0583_ok, packet0584_ok, packet0585_ok, packet0586_ok,
    packet0587_ok, packet0588_ok, packet0589_ok, packet0590_ok, packet0591_ok,
    packet0592_ok, packet0593_ok, packet0594_ok, packet0595_ok, packet0596_ok,
    packet0597_ok, packet0598_ok, packet0599_ok]

theorem packets024_valid : packets024.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
