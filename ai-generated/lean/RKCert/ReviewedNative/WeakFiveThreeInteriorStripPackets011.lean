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

def packet0264 : StripRowPacket :=
  ⟨⟨⟨8,11,5,8⟩,
    ![401,1310,2597,4087,5577,6866,7779],![438,1359,2644,4123,5602,6880,7786]⟩,
    ⟨-449843193024593616118845661309,93224963332536296316870189506560⟩,
    ⟨-46414701950696140974501223639,11186962820888753550245936742400⟩⟩

def packet0265 : StripRowPacket :=
  ⟨⟨⟨8,10,5,9⟩,
    ![432,1352,2636,4117,5597,6876,7782],![466,1401,2684,4156,5623,6891,7789]⟩,
    ⟨-90446786165418800447069764276207,21434754598410701040271227872051200⟩,
    ⟨-913345187744819788476614552877,257452980674807706600241877843968⟩⟩

def packet0266 : StripRowPacket :=
  ⟨⟨⟨8,11,5,9⟩,
    ![428,1347,2632,4114,5595,6875,7782],![462,1396,2680,4152,5621,6890,7789]⟩,
    ⟨-138181128483385332981097809507,32426074202621320458041805045760⟩,
    ⟨-20050246661208391225155843323,5593481410444376775122968371200⟩⟩

def packet0267 : StripRowPacket :=
  ⟨⟨⟨8,8,5,10⟩,
    ![464,1398,2680,4152,5619,6888,7786],![497,1447,2730,4193,5648,6904,7793]⟩,
    ⟨-5565983984724935697137747,1548841707520671335626455040⟩,
    ⟨-175619825084115195895084219,59926713566342848066039644160⟩⟩

def packet0268 : StripRowPacket :=
  ⟨⟨⟨8,9,5,10⟩,
    ![460,1393,2676,4148,5617,6887,7786],![492,1441,2725,4189,5646,6903,7793]⟩,
    ⟨-63052164036006198227458580115,17377269478483866989805912162304⟩,
    ⟨-4469099090279140328106073342609,1509506747372340137293148841410560⟩⟩

def packet0269 : StripRowPacket :=
  ⟨⟨⟨8,8,5,11⟩,
    ![486,1432,2716,4181,5639,6898,7789],![516,1480,2766,4224,5670,6916,7797]⟩,
    ⟨-122917689380936295085697201,40269884395537454726287831040⟩,
    ⟨-393641728569665157994037297,164798462307442832181609021440⟩⟩

def packet0270 : StripRowPacket :=
  ⟨⟨⟨8,9,5,11⟩,
    ![481,1427,2712,4178,5637,6897,7789],![510,1474,2762,4221,5668,6915,7797]⟩,
    ⟨-48646712607193813036424140691,15797517707712606354369011056640⟩,
    ⟨-181971243957939175540810152453,75475337368617006864657442070528⟩⟩

def packet0271 : StripRowPacket :=
  ⟨⟨⟨8,10,5,10⟩,
    ![456,1388,2672,4145,5615,6886,7785],![487,1436,2721,4186,5644,6902,7793]⟩,
    ⟨-39258341803950116612167718831699,10717377299205350520135613936025600⟩,
    ⟨-7699133035354168232920954392559,2574529806748077066002418778439680⟩⟩

def packet0272 : StripRowPacket :=
  ⟨⟨⟨8,11,5,10⟩,
    ![452,1383,2668,4142,5613,6885,7785],![482,1431,2716,4183,5642,6901,7792]⟩,
    ⟨-25068966963990694437997581335,6779997333275367004863286509568⟩,
    ⟨-33786284694137423926122149653,11186962820888753550245936742400⟩⟩

def packet0273 : StripRowPacket :=
  ⟨⟨⟨7,5,5,11⟩,
    ![471,1415,2701,4170,5632,6894,7788],![507,1471,2760,4220,5668,6915,7797]⟩,
    ⟨-1335175122160444865721759205,420218918953956108996802084864⟩,
    ⟨-5873177583241192484166547,2460528258748828047511187456⟩⟩

def packet0274 : StripRowPacket :=
  ⟨⟨⟨8,12,5,8⟩,
    ![398,1306,2593,4084,5575,6865,7779],![434,1355,2639,4120,5600,6879,7785]⟩,
    ⟨-1060240198122892567858611509,217532882436249088785091119104⟩,
    ⟨-9052537413032040762809242677,2159121430876468722264890212352⟩⟩

def packet0275 : StripRowPacket :=
  ⟨⟨⟨8,13,5,8⟩,
    ![395,1302,2590,4081,5573,6864,7778],![431,1350,2635,4117,5598,6878,7785]⟩,
    ⟨-17572009964289846209559242267,3570127811992349129309031096320⟩,
    ⟨-500830380665056703672169584993,118236452259449736503755369185280⟩⟩

def packet0276 : StripRowPacket :=
  ⟨⟨⟨8,12,5,9⟩,
    ![425,1343,2628,4111,5593,6874,7782],![458,1391,2675,4149,5619,6889,7788]⟩,
    ⟨-46509528419519947683486565,10809087326024799442737446912⟩,
    ⟨-8173838788581509379054066341,2257263314098126391458748858368⟩⟩

def packet0277 : StripRowPacket :=
  ⟨⟨⟨8,13,5,9⟩,
    ![422,1339,2624,4108,5591,6873,7781],![454,1387,2671,4146,5617,6888,7788]⟩,
    ⟨-1364702626980833719424821635377,314171247455326723379194736476160⟩,
    ⟨-994575244824717263043154187007,271943840196734393958637349126144⟩⟩

def packet0278 : StripRowPacket :=
  ⟨⟨⟨7,7,5,8⟩,
    ![388,1292,2580,4074,5568,6861,7778],![429,1348,2633,4116,5597,6877,7785]⟩,
    ⟨-1777695387384112017299,352361088641933344624640⟩,
    ⟨-251640863567687978077,59253583314933543847168⟩⟩

def packet0279 : StripRowPacket :=
  ⟨⟨⟨7,7,5,9⟩,
    ![415,1329,2615,4101,5586,6870,7781],![452,1384,2670,4145,5616,6888,7788]⟩,
    ⟨-163326570910843754364719,36645553218761067840962560⟩,
    ⟨-135466061483796103909,37033489571833464904480⟩⟩

def packet0280 : StripRowPacket :=
  ⟨⟨⟨7,6,5,10⟩,
    ![443,1372,2658,4134,5608,6882,7784],![480,1428,2715,4182,5641,6901,7792]⟩,
    ⟨-34301334646508792097229711,9018704743563831964870942720⟩,
    ⟨-1915230706412033906077129721,636471434711302648841175203840⟩⟩

def packet0281 : StripRowPacket :=
  ⟨⟨⟨7,6,5,11⟩,
    ![464,1407,2693,4164,5628,6893,7788],![498,1461,2752,4214,5664,6913,7796]⟩,
    ⟨-58242518177564822501784161,18037409487127663929741885440⟩,
    ⟨-387276417375373116778606113,159117858677825662210293800960⟩⟩

def packet0282 : StripRowPacket :=
  ⟨⟨⟨7,7,5,10⟩,
    ![437,1365,2650,4129,5605,6880,7784],![472,1419,2706,4176,5637,6899,7792]⟩,
    ⟨-70886410766869929465171,18322776609380533920481280⟩,
    ⟨-69942512761715213243,22789839736512901479680⟩⟩

def packet0283 : StripRowPacket :=
  ⟨⟨⟨7,7,5,11⟩,
    ![457,1399,2686,4159,5625,6891,7787],![490,1452,2743,4208,5660,6911,7795]⟩,
    ⟨-24043814431327192699193,7329110643752213568192512⟩,
    ⟨-367388419967113356523,148133958287333859617920⟩⟩

def packet0284 : StripRowPacket :=
  ⟨⟨⟨7,4,5,12⟩,
    ![498,1457,2745,4206,5657,6908,7792],![534,1514,2807,4261,5696,6930,7802]⟩,
    ⟨-649275725999526566738911,251541703711133941822306304⟩,
    ⟨-9868459736695294489143115,5502789851147217548216467456⟩⟩

def packet0285 : StripRowPacket :=
  ⟨⟨⟨7,4,5,13⟩,
    ![514,1488,2781,4238,5680,6920,7796],![548,1543,2844,4295,5722,6944,7806]⟩,
    ⟨-2048941400541019460139393,1006166814844535767289225216⟩,
    ⟨-44613692823941922420087053,35768134032456914063407038464⟩⟩

def packet0286 : StripRowPacket :=
  ⟨⟨⟨7,5,5,12⟩,
    ![489,1448,2737,4201,5653,6906,7792],![523,1503,2797,4254,5692,6928,7801]⟩,
    ⟨-274968220767860188195516653,105054729738489027249200521216⟩,
    ⟨-17971408797371381367170205,9842113034995312190044749824⟩⟩

def packet0287 : StripRowPacket :=
  ⟨⟨⟨7,5,5,13⟩,
    ![505,1479,2773,4233,5676,6918,7796],![537,1532,2834,4288,5718,6942,7806]⟩,
    ⟨-864570643982436639842374019,420218918953956108996802084864⟩,
    ⟨-80844852349207745439443,63909824902566962273017856⟩⟩

def packets011 : List StripRowPacket :=
  [packet0264, packet0265, packet0266, packet0267, packet0268, packet0269,
   packet0270, packet0271, packet0272, packet0273, packet0274, packet0275,
   packet0276, packet0277, packet0278, packet0279, packet0280, packet0281,
   packet0282, packet0283, packet0284, packet0285, packet0286, packet0287]

theorem packet0264_membership : packet0264 ∈ packets011 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0264_shape : checkStripShape packet0264.row = true := by
  decide +kernel

private theorem packet0264_cache : checkStripCache packet0264 = true := by
  decide +kernel

private theorem packet0264_pair (i : Fin 7) : checkEdgePair packet0264 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0264_ok : checkStripPacket packet0264 = true :=
  checkStripPacket_intro packet0264_shape packet0264_cache packet0264_pair

theorem packet0265_membership : packet0265 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0265_shape : checkStripShape packet0265.row = true := by
  decide +kernel

private theorem packet0265_cache : checkStripCache packet0265 = true := by
  decide +kernel

private theorem packet0265_pair (i : Fin 7) : checkEdgePair packet0265 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0265_ok : checkStripPacket packet0265 = true :=
  checkStripPacket_intro packet0265_shape packet0265_cache packet0265_pair

theorem packet0266_membership : packet0266 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0266_shape : checkStripShape packet0266.row = true := by
  decide +kernel

private theorem packet0266_cache : checkStripCache packet0266 = true := by
  decide +kernel

private theorem packet0266_pair (i : Fin 7) : checkEdgePair packet0266 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0266_ok : checkStripPacket packet0266 = true :=
  checkStripPacket_intro packet0266_shape packet0266_cache packet0266_pair

theorem packet0267_membership : packet0267 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0267_shape : checkStripShape packet0267.row = true := by
  decide +kernel

private theorem packet0267_cache : checkStripCache packet0267 = true := by
  decide +kernel

private theorem packet0267_pair (i : Fin 7) : checkEdgePair packet0267 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0267_ok : checkStripPacket packet0267 = true :=
  checkStripPacket_intro packet0267_shape packet0267_cache packet0267_pair

theorem packet0268_membership : packet0268 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0268_shape : checkStripShape packet0268.row = true := by
  decide +kernel

private theorem packet0268_cache : checkStripCache packet0268 = true := by
  decide +kernel

private theorem packet0268_pair (i : Fin 7) : checkEdgePair packet0268 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0268_ok : checkStripPacket packet0268 = true :=
  checkStripPacket_intro packet0268_shape packet0268_cache packet0268_pair

theorem packet0269_membership : packet0269 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0269_shape : checkStripShape packet0269.row = true := by
  decide +kernel

private theorem packet0269_cache : checkStripCache packet0269 = true := by
  decide +kernel

private theorem packet0269_pair (i : Fin 7) : checkEdgePair packet0269 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0269_ok : checkStripPacket packet0269 = true :=
  checkStripPacket_intro packet0269_shape packet0269_cache packet0269_pair

theorem packet0270_membership : packet0270 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0270_shape : checkStripShape packet0270.row = true := by
  decide +kernel

private theorem packet0270_cache : checkStripCache packet0270 = true := by
  decide +kernel

private theorem packet0270_pair (i : Fin 7) : checkEdgePair packet0270 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0270_ok : checkStripPacket packet0270 = true :=
  checkStripPacket_intro packet0270_shape packet0270_cache packet0270_pair

theorem packet0271_membership : packet0271 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0271_shape : checkStripShape packet0271.row = true := by
  decide +kernel

private theorem packet0271_cache : checkStripCache packet0271 = true := by
  decide +kernel

private theorem packet0271_pair (i : Fin 7) : checkEdgePair packet0271 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0271_ok : checkStripPacket packet0271 = true :=
  checkStripPacket_intro packet0271_shape packet0271_cache packet0271_pair

theorem packet0272_membership : packet0272 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0272_shape : checkStripShape packet0272.row = true := by
  decide +kernel

private theorem packet0272_cache : checkStripCache packet0272 = true := by
  decide +kernel

private theorem packet0272_pair (i : Fin 7) : checkEdgePair packet0272 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0272_ok : checkStripPacket packet0272 = true :=
  checkStripPacket_intro packet0272_shape packet0272_cache packet0272_pair

theorem packet0273_membership : packet0273 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0273_shape : checkStripShape packet0273.row = true := by
  decide +kernel

private theorem packet0273_cache : checkStripCache packet0273 = true := by
  decide +kernel

private theorem packet0273_pair (i : Fin 7) : checkEdgePair packet0273 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0273_ok : checkStripPacket packet0273 = true :=
  checkStripPacket_intro packet0273_shape packet0273_cache packet0273_pair

theorem packet0274_membership : packet0274 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0274_shape : checkStripShape packet0274.row = true := by
  decide +kernel

private theorem packet0274_cache : checkStripCache packet0274 = true := by
  decide +kernel

private theorem packet0274_pair (i : Fin 7) : checkEdgePair packet0274 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0274_ok : checkStripPacket packet0274 = true :=
  checkStripPacket_intro packet0274_shape packet0274_cache packet0274_pair

theorem packet0275_membership : packet0275 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0275_shape : checkStripShape packet0275.row = true := by
  decide +kernel

private theorem packet0275_cache : checkStripCache packet0275 = true := by
  decide +kernel

private theorem packet0275_pair (i : Fin 7) : checkEdgePair packet0275 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0275_ok : checkStripPacket packet0275 = true :=
  checkStripPacket_intro packet0275_shape packet0275_cache packet0275_pair

theorem packet0276_membership : packet0276 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0276_shape : checkStripShape packet0276.row = true := by
  decide +kernel

private theorem packet0276_cache : checkStripCache packet0276 = true := by
  decide +kernel

private theorem packet0276_pair (i : Fin 7) : checkEdgePair packet0276 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0276_ok : checkStripPacket packet0276 = true :=
  checkStripPacket_intro packet0276_shape packet0276_cache packet0276_pair

theorem packet0277_membership : packet0277 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0277_shape : checkStripShape packet0277.row = true := by
  decide +kernel

private theorem packet0277_cache : checkStripCache packet0277 = true := by
  decide +kernel

private theorem packet0277_pair (i : Fin 7) : checkEdgePair packet0277 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0277_ok : checkStripPacket packet0277 = true :=
  checkStripPacket_intro packet0277_shape packet0277_cache packet0277_pair

theorem packet0278_membership : packet0278 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0278_shape : checkStripShape packet0278.row = true := by
  decide +kernel

private theorem packet0278_cache : checkStripCache packet0278 = true := by
  decide +kernel

private theorem packet0278_pair (i : Fin 7) : checkEdgePair packet0278 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0278_ok : checkStripPacket packet0278 = true :=
  checkStripPacket_intro packet0278_shape packet0278_cache packet0278_pair

theorem packet0279_membership : packet0279 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0279_shape : checkStripShape packet0279.row = true := by
  decide +kernel

private theorem packet0279_cache : checkStripCache packet0279 = true := by
  decide +kernel

private theorem packet0279_pair (i : Fin 7) : checkEdgePair packet0279 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0279_ok : checkStripPacket packet0279 = true :=
  checkStripPacket_intro packet0279_shape packet0279_cache packet0279_pair

theorem packet0280_membership : packet0280 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0280_shape : checkStripShape packet0280.row = true := by
  decide +kernel

private theorem packet0280_cache : checkStripCache packet0280 = true := by
  decide +kernel

private theorem packet0280_pair (i : Fin 7) : checkEdgePair packet0280 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0280_ok : checkStripPacket packet0280 = true :=
  checkStripPacket_intro packet0280_shape packet0280_cache packet0280_pair

theorem packet0281_membership : packet0281 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0281_shape : checkStripShape packet0281.row = true := by
  decide +kernel

private theorem packet0281_cache : checkStripCache packet0281 = true := by
  decide +kernel

private theorem packet0281_pair (i : Fin 7) : checkEdgePair packet0281 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0281_ok : checkStripPacket packet0281 = true :=
  checkStripPacket_intro packet0281_shape packet0281_cache packet0281_pair

theorem packet0282_membership : packet0282 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0282_shape : checkStripShape packet0282.row = true := by
  decide +kernel

private theorem packet0282_cache : checkStripCache packet0282 = true := by
  decide +kernel

private theorem packet0282_pair (i : Fin 7) : checkEdgePair packet0282 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0282_ok : checkStripPacket packet0282 = true :=
  checkStripPacket_intro packet0282_shape packet0282_cache packet0282_pair

theorem packet0283_membership : packet0283 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0283_shape : checkStripShape packet0283.row = true := by
  decide +kernel

private theorem packet0283_cache : checkStripCache packet0283 = true := by
  decide +kernel

private theorem packet0283_pair (i : Fin 7) : checkEdgePair packet0283 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0283_ok : checkStripPacket packet0283 = true :=
  checkStripPacket_intro packet0283_shape packet0283_cache packet0283_pair

theorem packet0284_membership : packet0284 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0284_shape : checkStripShape packet0284.row = true := by
  decide +kernel

private theorem packet0284_cache : checkStripCache packet0284 = true := by
  decide +kernel

private theorem packet0284_pair (i : Fin 7) : checkEdgePair packet0284 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0284_ok : checkStripPacket packet0284 = true :=
  checkStripPacket_intro packet0284_shape packet0284_cache packet0284_pair

theorem packet0285_membership : packet0285 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0285_shape : checkStripShape packet0285.row = true := by
  decide +kernel

private theorem packet0285_cache : checkStripCache packet0285 = true := by
  decide +kernel

private theorem packet0285_pair (i : Fin 7) : checkEdgePair packet0285 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0285_ok : checkStripPacket packet0285 = true :=
  checkStripPacket_intro packet0285_shape packet0285_cache packet0285_pair

theorem packet0286_membership : packet0286 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0286_shape : checkStripShape packet0286.row = true := by
  decide +kernel

private theorem packet0286_cache : checkStripCache packet0286 = true := by
  decide +kernel

private theorem packet0286_pair (i : Fin 7) : checkEdgePair packet0286 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0286_ok : checkStripPacket packet0286 = true :=
  checkStripPacket_intro packet0286_shape packet0286_cache packet0286_pair

theorem packet0287_membership : packet0287 ∈ packets011 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0287_shape : checkStripShape packet0287.row = true := by
  decide +kernel

private theorem packet0287_cache : checkStripCache packet0287 = true := by
  decide +kernel

private theorem packet0287_pair (i : Fin 7) : checkEdgePair packet0287 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0287_ok : checkStripPacket packet0287 = true :=
  checkStripPacket_intro packet0287_shape packet0287_cache packet0287_pair

theorem packets011_checked : packets011.all checkStripPacket = true := by
  simp only [packets011, List.all_cons, List.all_nil, Bool.true_and, packet0264_ok,
    packet0265_ok, packet0266_ok, packet0267_ok, packet0268_ok, packet0269_ok,
    packet0270_ok, packet0271_ok, packet0272_ok, packet0273_ok, packet0274_ok,
    packet0275_ok, packet0276_ok, packet0277_ok, packet0278_ok, packet0279_ok,
    packet0280_ok, packet0281_ok, packet0282_ok, packet0283_ok, packet0284_ok,
    packet0285_ok, packet0286_ok, packet0287_ok]

theorem packets011_valid : packets011.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
