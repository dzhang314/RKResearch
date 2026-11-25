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

def packet0984 : StripRowPacket :=
  ⟨⟨⟨6,44,4,11⟩,
    ![449,1439,2807,4342,5820,7035,7846],![461,1469,2860,4417,5906,7113,7887]⟩,
    ⟨140160092000996980399807,19060479547373547821824000⟩,
    ⟨55899266509498444775580287,5557973490558632549455329280⟩⟩

def packet0985 : StripRowPacket :=
  ⟨⟨⟨6,45,4,11⟩,
    ![449,1437,2804,4340,5818,7034,7845],![461,1467,2858,4415,5904,7112,7887]⟩,
    ⟨181522582469973998393167119,24423204516833129514543669248⟩,
    ⟨119646136402897929641382417,11775483239039325164238330880⟩⟩

def packet0986 : StripRowPacket :=
  ⟨⟨⟨6,46,5,20⟩,
    ![439,1409,2753,4271,5744,6976,7820],![449,1430,2789,4317,5792,7014,7838]⟩,
    ⟨442550765072565544130408539,89208489278534572067974780928⟩,
    ⟨23169772775265436958088822803,3599051441380935025977735495680⟩⟩

def packet0987 : StripRowPacket :=
  ⟨⟨⟨6,46,5,21⟩,
    ![444,1423,2778,4305,5780,7004,7832],![453,1443,2812,4350,5829,7044,7852]⟩,
    ⟨1011439337300632228885742821,162197253233699221941772328960⟩,
    ⟨2775907010107477583962689321,359905144138093502597773549568⟩⟩

def packet0988 : StripRowPacket :=
  ⟨⟨⟨6,47,5,20⟩,
    ![439,1407,2751,4268,5742,6975,7820],![448,1429,2786,4315,5791,7013,7837]⟩,
    ⟨19144900657996137991051,3818433006286728442376192⟩,
    ⟨66944421146208383651,10295771045278058948608⟩⟩

def packet0989 : StripRowPacket :=
  ⟨⟨⟨6,47,5,21⟩,
    ![443,1421,2776,4302,5778,7003,7831],![452,1441,2810,4348,5827,7043,7851]⟩,
    ⟨96245146409577113207931,15273732025146913769504768⟩,
    ⟨441111435485550205007,56626740749029324217344⟩⟩

def packet0990 : StripRowPacket :=
  ⟨⟨⟨6,46,4,11⟩,
    ![448,1436,2802,4338,5816,7033,7845],![460,1466,2855,4412,5902,7111,7887]⟩,
    ⟨6700325059581299076439085641,892084892785345720679747809280⟩,
    ⟨4617208094086681700337879253,449881430172616878247216936960⟩⟩

def packet0991 : StripRowPacket :=
  ⟨⟨⟨6,47,4,11⟩,
    ![448,1434,2799,4335,5814,7032,7845],![459,1464,2852,4409,5900,7110,7886]⟩,
    ⟨57955345093584837225829,7636866012573456884752384⟩,
    ⟨146736418462089598715,14156685187257331054336⟩⟩

def packet0992 : StripRowPacket :=
  ⟨⟨⟨5,20,4,12⟩,
    ![459,1466,2855,4408,5893,7099,7877],![471,1498,2912,4488,5989,7195,7940]⟩,
    ⟨92844006211338042183,9900353763224708582656⟩,
    ⟨115958847681038407915,9500246795864876699648⟩⟩

def packet0993 : StripRowPacket :=
  ⟨⟨⟨5,20,4,13⟩,
    ![465,1486,2893,4464,5963,7169,7921],![476,1515,2944,4538,6054,7269,8007]⟩,
    ⟨466784434840789835441,39601415052898834330624⟩,
    ⟨5340480144762892581,365394107533264488448⟩⟩

def packet0994 : StripRowPacket :=
  ⟨⟨⟨5,21,4,12⟩,
    ![457,1462,2850,4403,5890,7097,7877],![469,1494,2906,4482,5985,7192,7939]⟩,
    ⟨2831731597090274792623,295226719550240417438720⟩,
    ⟨4851721074629455288961,389191387762050674944000⟩⟩

def packet0995 : StripRowPacket :=
  ⟨⟨⟨5,21,4,13⟩,
    ![463,1482,2887,4459,5959,7167,7921],![475,1511,2938,4532,6050,7267,8006]⟩,
    ⟨156563027663790582353579,12989975660210578367303680⟩,
    ⟨2904849100583660326979,194595693881025337472000⟩⟩

def packet0996 : StripRowPacket :=
  ⟨⟨⟨5,20,4,14⟩,
    ![470,1503,2926,4515,6028,7242,7981],![481,1530,2972,4581,6112,7340,8098]⟩,
    ⟨25554220219828522825,1800064320586310651392⟩,
    ⟨161746119846632006297,9500246795864876699648⟩⟩

def packet0997 : StripRowPacket :=
  ⟨⟨⟨5,20,4,15⟩,
    ![475,1518,2955,4559,6087,7313,8062],![485,1543,2997,4619,6163,7401,8192]⟩,
    ⟨657601254831665168859,39601415052898834330624⟩,
    ⟨3511785874991,180691489428736⟩⟩

def packet0998 : StripRowPacket :=
  ⟨⟨⟨5,21,4,14⟩,
    ![469,1499,2920,4509,6025,7240,7981],![479,1526,2966,4575,6108,7337,8097]⟩,
    ⟨94264932527804536915873,6494987830105289183651840⟩,
    ⟨1353535065541037203791,77838277552410134988800⟩⟩

def packet0999 : StripRowPacket :=
  ⟨⟨⟨5,21,4,15⟩,
    ![473,1514,2949,4554,6084,7311,8062],![483,1538,2991,4613,6159,7399,8192]⟩,
    ⟨220496702447427565309913,12989975660210578367303680⟩,
    ⟨20671955371,1041380912000⟩⟩

def packet1000 : StripRowPacket :=
  ⟨⟨⟨6,44,4,12⟩,
    ![457,1462,2850,4404,5892,7100,7879],![468,1489,2898,4473,5976,7185,7935]⟩,
    ⟨46950042439858587607311,4765119886843386955456000⟩,
    ⟨279170118754024016807402321,22231893962234530197821317120⟩⟩

def packet1001 : StripRowPacket :=
  ⟨⟨⟨6,45,4,12⟩,
    ![456,1460,2847,4402,5890,7099,7879],![467,1487,2895,4470,5974,7184,7934]⟩,
    ⟨3951769780500277977874979239,396877073398538354611334625280⟩,
    ⟨597519892322879635981674767,47101932956157300656953323520⟩⟩

def packet1002 : StripRowPacket :=
  ⟨⟨⟨5,22,4,13⟩,
    ![462,1479,2882,4454,5956,7166,7921],![473,1507,2932,4526,6046,7265,8005]⟩,
    ⟨1196969402845693920973,97197949604968539392000⟩,
    ⟨56374553351150667284921,3700114429297303951538176⟩⟩

def packet1003 : StripRowPacket :=
  ⟨⟨⟨6,46,4,12⟩,
    ![455,1458,2845,4399,5889,7099,7879],![466,1485,2892,4468,5972,7183,7934]⟩,
    ⟨2243785617109235677893521473,223021223196336430169936952320⟩,
    ⟨23058129702156065682889587419,1799525720690467512988867747840⟩⟩

def packet1004 : StripRowPacket :=
  ⟨⟨⟨6,47,4,12⟩,
    ![455,1457,2842,4397,5887,7098,7878],![465,1483,2890,4465,5970,7182,7934]⟩,
    ⟨19405222217794349617389,1909216503143364221188096⟩,
    ⟨56367685554705121901,4355903134540717247488⟩⟩

def packet1005 : StripRowPacket :=
  ⟨⟨⟨5,23,4,13⟩,
    ![461,1475,2877,4449,5952,7164,7920],![472,1503,2927,4520,6041,7263,8005]⟩,
    ⟨704931999053332543483,56063707287359945338880⟩,
    ⟨1629004218272189307,104821433351989777280⟩⟩

def packet1006 : StripRowPacket :=
  ⟨⟨⟨5,22,4,14⟩,
    ![467,1496,2915,4504,6021,7239,7981],![478,1521,2960,4569,6104,7335,8096]⟩,
    ⟨7926176325707218721517,534588722827326966656000⟩,
    ⟨656710372276378040741621,37001144292973039515381760⟩⟩

def packet1007 : StripRowPacket :=
  ⟨⟨⟨5,22,4,15⟩,
    ![472,1510,2944,4549,6080,7310,8063],![482,1534,2985,4608,6154,7397,8192]⟩,
    ⟨3707608374305248351073,213835489130930786662400⟩,
    ⟨52140178709407,2573442802261760⟩⟩

def packets041 : List StripRowPacket :=
  [packet0984, packet0985, packet0986, packet0987, packet0988, packet0989,
   packet0990, packet0991, packet0992, packet0993, packet0994, packet0995,
   packet0996, packet0997, packet0998, packet0999, packet1000, packet1001,
   packet1002, packet1003, packet1004, packet1005, packet1006, packet1007]

theorem packet0984_membership : packet0984 ∈ packets041 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0984_shape : checkStripShape packet0984.row = true := by
  decide +kernel

private theorem packet0984_cache : checkStripCache packet0984 = true := by
  decide +kernel

private theorem packet0984_pair (i : Fin 7) : checkEdgePair packet0984 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0984_ok : checkStripPacket packet0984 = true :=
  checkStripPacket_intro packet0984_shape packet0984_cache packet0984_pair

theorem packet0985_membership : packet0985 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0985_shape : checkStripShape packet0985.row = true := by
  decide +kernel

private theorem packet0985_cache : checkStripCache packet0985 = true := by
  decide +kernel

private theorem packet0985_pair (i : Fin 7) : checkEdgePair packet0985 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0985_ok : checkStripPacket packet0985 = true :=
  checkStripPacket_intro packet0985_shape packet0985_cache packet0985_pair

theorem packet0986_membership : packet0986 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0986_shape : checkStripShape packet0986.row = true := by
  decide +kernel

private theorem packet0986_cache : checkStripCache packet0986 = true := by
  decide +kernel

private theorem packet0986_pair (i : Fin 7) : checkEdgePair packet0986 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0986_ok : checkStripPacket packet0986 = true :=
  checkStripPacket_intro packet0986_shape packet0986_cache packet0986_pair

theorem packet0987_membership : packet0987 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0987_shape : checkStripShape packet0987.row = true := by
  decide +kernel

private theorem packet0987_cache : checkStripCache packet0987 = true := by
  decide +kernel

private theorem packet0987_pair (i : Fin 7) : checkEdgePair packet0987 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0987_ok : checkStripPacket packet0987 = true :=
  checkStripPacket_intro packet0987_shape packet0987_cache packet0987_pair

theorem packet0988_membership : packet0988 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0988_shape : checkStripShape packet0988.row = true := by
  decide +kernel

private theorem packet0988_cache : checkStripCache packet0988 = true := by
  decide +kernel

private theorem packet0988_pair (i : Fin 7) : checkEdgePair packet0988 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0988_ok : checkStripPacket packet0988 = true :=
  checkStripPacket_intro packet0988_shape packet0988_cache packet0988_pair

theorem packet0989_membership : packet0989 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0989_shape : checkStripShape packet0989.row = true := by
  decide +kernel

private theorem packet0989_cache : checkStripCache packet0989 = true := by
  decide +kernel

private theorem packet0989_pair (i : Fin 7) : checkEdgePair packet0989 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0989_ok : checkStripPacket packet0989 = true :=
  checkStripPacket_intro packet0989_shape packet0989_cache packet0989_pair

theorem packet0990_membership : packet0990 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0990_shape : checkStripShape packet0990.row = true := by
  decide +kernel

private theorem packet0990_cache : checkStripCache packet0990 = true := by
  decide +kernel

private theorem packet0990_pair (i : Fin 7) : checkEdgePair packet0990 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0990_ok : checkStripPacket packet0990 = true :=
  checkStripPacket_intro packet0990_shape packet0990_cache packet0990_pair

theorem packet0991_membership : packet0991 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0991_shape : checkStripShape packet0991.row = true := by
  decide +kernel

private theorem packet0991_cache : checkStripCache packet0991 = true := by
  decide +kernel

private theorem packet0991_pair (i : Fin 7) : checkEdgePair packet0991 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0991_ok : checkStripPacket packet0991 = true :=
  checkStripPacket_intro packet0991_shape packet0991_cache packet0991_pair

theorem packet0992_membership : packet0992 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0992_shape : checkStripShape packet0992.row = true := by
  decide +kernel

private theorem packet0992_cache : checkStripCache packet0992 = true := by
  decide +kernel

private theorem packet0992_pair (i : Fin 7) : checkEdgePair packet0992 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0992_ok : checkStripPacket packet0992 = true :=
  checkStripPacket_intro packet0992_shape packet0992_cache packet0992_pair

theorem packet0993_membership : packet0993 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0993_shape : checkStripShape packet0993.row = true := by
  decide +kernel

private theorem packet0993_cache : checkStripCache packet0993 = true := by
  decide +kernel

private theorem packet0993_pair (i : Fin 7) : checkEdgePair packet0993 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0993_ok : checkStripPacket packet0993 = true :=
  checkStripPacket_intro packet0993_shape packet0993_cache packet0993_pair

theorem packet0994_membership : packet0994 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0994_shape : checkStripShape packet0994.row = true := by
  decide +kernel

private theorem packet0994_cache : checkStripCache packet0994 = true := by
  decide +kernel

private theorem packet0994_pair (i : Fin 7) : checkEdgePair packet0994 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0994_ok : checkStripPacket packet0994 = true :=
  checkStripPacket_intro packet0994_shape packet0994_cache packet0994_pair

theorem packet0995_membership : packet0995 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0995_shape : checkStripShape packet0995.row = true := by
  decide +kernel

private theorem packet0995_cache : checkStripCache packet0995 = true := by
  decide +kernel

private theorem packet0995_pair (i : Fin 7) : checkEdgePair packet0995 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0995_ok : checkStripPacket packet0995 = true :=
  checkStripPacket_intro packet0995_shape packet0995_cache packet0995_pair

theorem packet0996_membership : packet0996 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0996_shape : checkStripShape packet0996.row = true := by
  decide +kernel

private theorem packet0996_cache : checkStripCache packet0996 = true := by
  decide +kernel

private theorem packet0996_pair (i : Fin 7) : checkEdgePair packet0996 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0996_ok : checkStripPacket packet0996 = true :=
  checkStripPacket_intro packet0996_shape packet0996_cache packet0996_pair

theorem packet0997_membership : packet0997 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0997_shape : checkStripShape packet0997.row = true := by
  decide +kernel

private theorem packet0997_cache : checkStripCache packet0997 = true := by
  decide +kernel

private theorem packet0997_pair (i : Fin 7) : checkEdgePair packet0997 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0997_ok : checkStripPacket packet0997 = true :=
  checkStripPacket_intro packet0997_shape packet0997_cache packet0997_pair

theorem packet0998_membership : packet0998 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0998_shape : checkStripShape packet0998.row = true := by
  decide +kernel

private theorem packet0998_cache : checkStripCache packet0998 = true := by
  decide +kernel

private theorem packet0998_pair (i : Fin 7) : checkEdgePair packet0998 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0998_ok : checkStripPacket packet0998 = true :=
  checkStripPacket_intro packet0998_shape packet0998_cache packet0998_pair

theorem packet0999_membership : packet0999 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0999_shape : checkStripShape packet0999.row = true := by
  decide +kernel

private theorem packet0999_cache : checkStripCache packet0999 = true := by
  decide +kernel

private theorem packet0999_pair (i : Fin 7) : checkEdgePair packet0999 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0999_ok : checkStripPacket packet0999 = true :=
  checkStripPacket_intro packet0999_shape packet0999_cache packet0999_pair

theorem packet1000_membership : packet1000 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet1000_shape : checkStripShape packet1000.row = true := by
  decide +kernel

private theorem packet1000_cache : checkStripCache packet1000 = true := by
  decide +kernel

private theorem packet1000_pair (i : Fin 7) : checkEdgePair packet1000 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1000_ok : checkStripPacket packet1000 = true :=
  checkStripPacket_intro packet1000_shape packet1000_cache packet1000_pair

theorem packet1001_membership : packet1001 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet1001_shape : checkStripShape packet1001.row = true := by
  decide +kernel

private theorem packet1001_cache : checkStripCache packet1001 = true := by
  decide +kernel

private theorem packet1001_pair (i : Fin 7) : checkEdgePair packet1001 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1001_ok : checkStripPacket packet1001 = true :=
  checkStripPacket_intro packet1001_shape packet1001_cache packet1001_pair

theorem packet1002_membership : packet1002 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet1002_shape : checkStripShape packet1002.row = true := by
  decide +kernel

private theorem packet1002_cache : checkStripCache packet1002 = true := by
  decide +kernel

private theorem packet1002_pair (i : Fin 7) : checkEdgePair packet1002 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1002_ok : checkStripPacket packet1002 = true :=
  checkStripPacket_intro packet1002_shape packet1002_cache packet1002_pair

theorem packet1003_membership : packet1003 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet1003_shape : checkStripShape packet1003.row = true := by
  decide +kernel

private theorem packet1003_cache : checkStripCache packet1003 = true := by
  decide +kernel

private theorem packet1003_pair (i : Fin 7) : checkEdgePair packet1003 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1003_ok : checkStripPacket packet1003 = true :=
  checkStripPacket_intro packet1003_shape packet1003_cache packet1003_pair

theorem packet1004_membership : packet1004 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet1004_shape : checkStripShape packet1004.row = true := by
  decide +kernel

private theorem packet1004_cache : checkStripCache packet1004 = true := by
  decide +kernel

private theorem packet1004_pair (i : Fin 7) : checkEdgePair packet1004 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1004_ok : checkStripPacket packet1004 = true :=
  checkStripPacket_intro packet1004_shape packet1004_cache packet1004_pair

theorem packet1005_membership : packet1005 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet1005_shape : checkStripShape packet1005.row = true := by
  decide +kernel

private theorem packet1005_cache : checkStripCache packet1005 = true := by
  decide +kernel

private theorem packet1005_pair (i : Fin 7) : checkEdgePair packet1005 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1005_ok : checkStripPacket packet1005 = true :=
  checkStripPacket_intro packet1005_shape packet1005_cache packet1005_pair

theorem packet1006_membership : packet1006 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1006_shape : checkStripShape packet1006.row = true := by
  decide +kernel

private theorem packet1006_cache : checkStripCache packet1006 = true := by
  decide +kernel

private theorem packet1006_pair (i : Fin 7) : checkEdgePair packet1006 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1006_ok : checkStripPacket packet1006 = true :=
  checkStripPacket_intro packet1006_shape packet1006_cache packet1006_pair

theorem packet1007_membership : packet1007 ∈ packets041 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1007_shape : checkStripShape packet1007.row = true := by
  decide +kernel

private theorem packet1007_cache : checkStripCache packet1007 = true := by
  decide +kernel

private theorem packet1007_pair (i : Fin 7) : checkEdgePair packet1007 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1007_ok : checkStripPacket packet1007 = true :=
  checkStripPacket_intro packet1007_shape packet1007_cache packet1007_pair

theorem packets041_checked : packets041.all checkStripPacket = true := by
  simp only [packets041, List.all_cons, List.all_nil, Bool.true_and, packet0984_ok,
    packet0985_ok, packet0986_ok, packet0987_ok, packet0988_ok, packet0989_ok,
    packet0990_ok, packet0991_ok, packet0992_ok, packet0993_ok, packet0994_ok,
    packet0995_ok, packet0996_ok, packet0997_ok, packet0998_ok, packet0999_ok,
    packet1000_ok, packet1001_ok, packet1002_ok, packet1003_ok, packet1004_ok,
    packet1005_ok, packet1006_ok, packet1007_ok]

theorem packets041_valid : packets041.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
