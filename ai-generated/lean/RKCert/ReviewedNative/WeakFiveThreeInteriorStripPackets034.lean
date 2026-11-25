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

def packet0816 : StripRowPacket :=
  ⟨⟨⟨6,29,4,8⟩,
    ![429,1374,2685,4177,5648,6907,7793],![448,1422,2761,4264,5726,6958,7813]⟩,
    ⟨-4493246872984983227189587,23295206442657612966307650560⟩,
    ⟨201365668453308287290306363,94424088314356768049525780480⟩⟩

def packet0817 : StripRowPacket :=
  ⟨⟨⟨6,28,4,9⟩,
    ![444,1415,2751,4252,5714,6949,7808],![461,1458,2821,4339,5798,7009,7833]⟩,
    ⟨1166580797356749621084617,623129180533554572223723520⟩,
    ⟨4769691502537529679121,1143381771056095443513344⟩⟩

def packet0818 : StripRowPacket :=
  ⟨⟨⟨6,29,4,9⟩,
    ![443,1412,2747,4249,5712,6948,7808],![459,1455,2817,4336,5795,7007,7832]⟩,
    ⟨354927166251074654236767477,186361651541260903730461204480⟩,
    ⟨199720344446014201337125967,47212044157178384024762890240⟩⟩

def packet0819 : StripRowPacket :=
  ⟨⟨⟨6,30,4,8⟩,
    ![428,1371,2681,4173,5645,6906,7793],![447,1420,2757,4261,5723,6956,7813]⟩,
    ⟨-233342559723473155313823,1233190730206891126132267520⟩,
    ⟨2542254633544130730145197,1175654813669513359861719040⟩⟩

def packet0820 : StripRowPacket :=
  ⟨⟨⟨6,31,4,8⟩,
    ![427,1369,2678,4170,5643,6904,7792],![446,1417,2753,4257,5720,6955,7812]⟩,
    ⟨-1864107941261099,10041244600102876160⟩,
    ⟨378870595648080727,172841375745973242880⟩⟩

def packet0821 : StripRowPacket :=
  ⟨⟨⟨6,30,4,9⟩,
    ![442,1410,2743,4245,5709,6946,7807],![458,1452,2813,4332,5793,7006,7832]⟩,
    ⟨19104660180345662197570129,9865525841655129009058140160⟩,
    ⟨504175190207916308335109,117565481366951335986171904⟩⟩

def packet0822 : StripRowPacket :=
  ⟨⟨⟨6,31,4,9⟩,
    ![440,1407,2740,4242,5707,6945,7807],![457,1449,2809,4328,5790,7004,7832]⟩,
    ⟨158101689615124349,80329956800823009280⟩,
    ⟨375595412367914803,86420687872986621440⟩⟩

def packet0823 : StripRowPacket :=
  ⟨⟨⟨6,28,4,10⟩,
    ![455,1448,2807,4323,5783,6997,7826],![470,1486,2871,4407,5871,7066,7858]⟩,
    ⟨1227848989107287681283733,311564590266777286111861760⟩,
    ⟨927612019600449944549247,148639630237292407656734720⟩⟩

def packet0824 : StripRowPacket :=
  ⟨⟨⟨6,29,4,10⟩,
    ![454,1445,2803,4319,5780,6995,7826],![468,1483,2867,4403,5868,7065,7858]⟩,
    ⟨74580030748602917429105165,18636165154126090373046120448⟩,
    ⟨119503141866149703611639501,18884817662871353609905156096⟩⟩

def packet0825 : StripRowPacket :=
  ⟨⟨⟨6,28,4,11⟩,
    ![464,1476,2857,4390,5854,7053,7851],![477,1509,2914,4469,5943,7132,7893]⟩,
    ⟨748963031814480220810063,124625836106710914444744704⟩,
    ⟨308791035967755257703191,37159907559323101914183680⟩⟩

def packet0826 : StripRowPacket :=
  ⟨⟨⟨6,29,4,11⟩,
    ![463,1473,2853,4387,5852,7051,7850],![476,1506,2910,4465,5941,7131,7892]⟩,
    ⟨87436419132383361103487371,14335511657020069517727784960⟩,
    ⟨198897682442367158360535769,23606022078589192012381445120⟩⟩

def packet0827 : StripRowPacket :=
  ⟨⟨⟨6,30,4,10⟩,
    ![453,1442,2799,4316,5778,6994,7826],![467,1480,2863,4399,5865,7064,7857]⟩,
    ⟨1821639129021777710802311,448432992802505864048097280⟩,
    ⟨7541249170614195436556983,1175654813669513359861719040⟩⟩

def packet0828 : StripRowPacket :=
  ⟨⟨⟨6,31,4,10⟩,
    ![451,1439,2796,4313,5775,6993,7825],![466,1477,2859,4396,5863,7062,7857]⟩,
    ⟨33111624276033749,8032995680082300928⟩,
    ⟨17284785443439669,2659098088399588352⟩⟩

def packet0829 : StripRowPacket :=
  ⟨⟨⟨6,30,4,11⟩,
    ![462,1470,2849,4383,5849,7050,7850],![475,1503,2906,4462,5938,7129,7892]⟩,
    ⟨939191715332500878118947,151777320640848138600894464⟩,
    ⟨2510186609787306947440719,293913703417378339965429760⟩⟩

def packet0830 : StripRowPacket :=
  ⟨⟨⟨6,31,4,11⟩,
    ![461,1467,2845,4380,5847,7049,7850],![474,1500,2902,4458,5936,7128,7891]⟩,
    ⟨504130795905550631,80329956800823009280⟩,
    ⟨373957820727831841,43210343936493310720⟩⟩

def packet0831 : StripRowPacket :=
  ⟨⟨⟨5,12,4,12⟩,
    ![476,1507,2909,4458,5927,7114,7880],![491,1546,2975,4547,6032,7217,7947]⟩,
    ⟨2290949560373665133,304100133150885111040⟩,
    ⟨31874852269632077863,3193588246752500879360⟩⟩

def packet0832 : StripRowPacket :=
  ⟨⟨⟨5,12,4,13⟩,
    ![482,1528,2948,4515,5996,7182,7922],![497,1564,3008,4597,6096,7291,8014]⟩,
    ⟨11555176800519549227,1216400532603540444160⟩,
    ⟨16142741756266282691,1351133489010673448960⟩⟩

def packet0833 : StripRowPacket :=
  ⟨⟨⟨5,13,4,12⟩,
    ![473,1501,2901,4451,5922,7112,7880],![488,1539,2965,4538,6025,7214,7945]⟩,
    ⟨1738810306537079768119,223475232211510413122560⟩,
    ⟨80364068601465267976271,7820215003738427929999360⟩⟩

def packet0834 : StripRowPacket :=
  ⟨⟨⟨5,13,4,13⟩,
    ![479,1521,2939,4507,5991,7181,7922],![493,1556,2998,4588,6090,7288,8013]⟩,
    ⟨8765415526050808156889,893900928846041652490240⟩,
    ⟨48102791880105799115437,3910107501869213964999680⟩⟩

def packet0835 : StripRowPacket :=
  ⟨⟨⟨5,12,4,14⟩,
    ![488,1546,2982,4565,6061,7254,7979],![502,1579,3037,4641,6154,7361,8106]⟩,
    ⟨6973277679772218961,608200266301770222080⟩,
    ⟨488799196359893843439,35129470714277509672960⟩⟩

def packet0836 : StripRowPacket :=
  ⟨⟨⟨5,12,4,15⟩,
    ![493,1562,3011,4610,6120,7325,8057],![506,1593,3062,4679,6205,7422,8192]⟩,
    ⟨16337933918569326617,1216400532603540444160⟩,
    ⟨9205374912397,579651231061760⟩⟩

def packet0837 : StripRowPacket :=
  ⟨⟨⟨5,13,4,14⟩,
    ![485,1539,2973,4558,6057,7253,7980],![498,1571,3027,4632,6148,7358,8104]⟩,
    ⟨5287794912976648620651,446950464423020826245120⟩,
    ⟨112047098918957928485477,7820215003738427929999360⟩⟩

def packet0838 : StripRowPacket :=
  ⟨⟨⟨5,13,4,15⟩,
    ![490,1555,3003,4603,6116,7323,8058],![502,1584,3052,4670,6199,7419,8192]⟩,
    ⟨225195711379196115013,16252744160837120954368⟩,
    ⟨88341752111,5401978122112⟩⟩

def packet0839 : StripRowPacket :=
  ⟨⟨⟨5,14,4,12⟩,
    ![470,1495,2893,4444,5918,7110,7879],![485,1531,2956,4530,6020,7211,7944]⟩,
    ⟨20947418563156834192881,2611183482522549678734848⟩,
    ⟨1212552326821954448545,114759189624084185403392⟩⟩

def packets034 : List StripRowPacket :=
  [packet0816, packet0817, packet0818, packet0819, packet0820, packet0821,
   packet0822, packet0823, packet0824, packet0825, packet0826, packet0827,
   packet0828, packet0829, packet0830, packet0831, packet0832, packet0833,
   packet0834, packet0835, packet0836, packet0837, packet0838, packet0839]

theorem packet0816_membership : packet0816 ∈ packets034 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0816_shape : checkStripShape packet0816.row = true := by
  decide +kernel

private theorem packet0816_cache : checkStripCache packet0816 = true := by
  decide +kernel

private theorem packet0816_pair (i : Fin 7) : checkEdgePair packet0816 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0816_ok : checkStripPacket packet0816 = true :=
  checkStripPacket_intro packet0816_shape packet0816_cache packet0816_pair

theorem packet0817_membership : packet0817 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0817_shape : checkStripShape packet0817.row = true := by
  decide +kernel

private theorem packet0817_cache : checkStripCache packet0817 = true := by
  decide +kernel

private theorem packet0817_pair (i : Fin 7) : checkEdgePair packet0817 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0817_ok : checkStripPacket packet0817 = true :=
  checkStripPacket_intro packet0817_shape packet0817_cache packet0817_pair

theorem packet0818_membership : packet0818 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0818_shape : checkStripShape packet0818.row = true := by
  decide +kernel

private theorem packet0818_cache : checkStripCache packet0818 = true := by
  decide +kernel

private theorem packet0818_pair (i : Fin 7) : checkEdgePair packet0818 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0818_ok : checkStripPacket packet0818 = true :=
  checkStripPacket_intro packet0818_shape packet0818_cache packet0818_pair

theorem packet0819_membership : packet0819 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0819_shape : checkStripShape packet0819.row = true := by
  decide +kernel

private theorem packet0819_cache : checkStripCache packet0819 = true := by
  decide +kernel

private theorem packet0819_pair (i : Fin 7) : checkEdgePair packet0819 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0819_ok : checkStripPacket packet0819 = true :=
  checkStripPacket_intro packet0819_shape packet0819_cache packet0819_pair

theorem packet0820_membership : packet0820 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0820_shape : checkStripShape packet0820.row = true := by
  decide +kernel

private theorem packet0820_cache : checkStripCache packet0820 = true := by
  decide +kernel

private theorem packet0820_pair (i : Fin 7) : checkEdgePair packet0820 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0820_ok : checkStripPacket packet0820 = true :=
  checkStripPacket_intro packet0820_shape packet0820_cache packet0820_pair

theorem packet0821_membership : packet0821 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0821_shape : checkStripShape packet0821.row = true := by
  decide +kernel

private theorem packet0821_cache : checkStripCache packet0821 = true := by
  decide +kernel

private theorem packet0821_pair (i : Fin 7) : checkEdgePair packet0821 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0821_ok : checkStripPacket packet0821 = true :=
  checkStripPacket_intro packet0821_shape packet0821_cache packet0821_pair

theorem packet0822_membership : packet0822 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0822_shape : checkStripShape packet0822.row = true := by
  decide +kernel

private theorem packet0822_cache : checkStripCache packet0822 = true := by
  decide +kernel

private theorem packet0822_pair (i : Fin 7) : checkEdgePair packet0822 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0822_ok : checkStripPacket packet0822 = true :=
  checkStripPacket_intro packet0822_shape packet0822_cache packet0822_pair

theorem packet0823_membership : packet0823 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0823_shape : checkStripShape packet0823.row = true := by
  decide +kernel

private theorem packet0823_cache : checkStripCache packet0823 = true := by
  decide +kernel

private theorem packet0823_pair (i : Fin 7) : checkEdgePair packet0823 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0823_ok : checkStripPacket packet0823 = true :=
  checkStripPacket_intro packet0823_shape packet0823_cache packet0823_pair

theorem packet0824_membership : packet0824 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0824_shape : checkStripShape packet0824.row = true := by
  decide +kernel

private theorem packet0824_cache : checkStripCache packet0824 = true := by
  decide +kernel

private theorem packet0824_pair (i : Fin 7) : checkEdgePair packet0824 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0824_ok : checkStripPacket packet0824 = true :=
  checkStripPacket_intro packet0824_shape packet0824_cache packet0824_pair

theorem packet0825_membership : packet0825 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0825_shape : checkStripShape packet0825.row = true := by
  decide +kernel

private theorem packet0825_cache : checkStripCache packet0825 = true := by
  decide +kernel

private theorem packet0825_pair (i : Fin 7) : checkEdgePair packet0825 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0825_ok : checkStripPacket packet0825 = true :=
  checkStripPacket_intro packet0825_shape packet0825_cache packet0825_pair

theorem packet0826_membership : packet0826 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0826_shape : checkStripShape packet0826.row = true := by
  decide +kernel

private theorem packet0826_cache : checkStripCache packet0826 = true := by
  decide +kernel

private theorem packet0826_pair (i : Fin 7) : checkEdgePair packet0826 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0826_ok : checkStripPacket packet0826 = true :=
  checkStripPacket_intro packet0826_shape packet0826_cache packet0826_pair

theorem packet0827_membership : packet0827 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0827_shape : checkStripShape packet0827.row = true := by
  decide +kernel

private theorem packet0827_cache : checkStripCache packet0827 = true := by
  decide +kernel

private theorem packet0827_pair (i : Fin 7) : checkEdgePair packet0827 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0827_ok : checkStripPacket packet0827 = true :=
  checkStripPacket_intro packet0827_shape packet0827_cache packet0827_pair

theorem packet0828_membership : packet0828 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0828_shape : checkStripShape packet0828.row = true := by
  decide +kernel

private theorem packet0828_cache : checkStripCache packet0828 = true := by
  decide +kernel

private theorem packet0828_pair (i : Fin 7) : checkEdgePair packet0828 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0828_ok : checkStripPacket packet0828 = true :=
  checkStripPacket_intro packet0828_shape packet0828_cache packet0828_pair

theorem packet0829_membership : packet0829 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0829_shape : checkStripShape packet0829.row = true := by
  decide +kernel

private theorem packet0829_cache : checkStripCache packet0829 = true := by
  decide +kernel

private theorem packet0829_pair (i : Fin 7) : checkEdgePair packet0829 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0829_ok : checkStripPacket packet0829 = true :=
  checkStripPacket_intro packet0829_shape packet0829_cache packet0829_pair

theorem packet0830_membership : packet0830 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0830_shape : checkStripShape packet0830.row = true := by
  decide +kernel

private theorem packet0830_cache : checkStripCache packet0830 = true := by
  decide +kernel

private theorem packet0830_pair (i : Fin 7) : checkEdgePair packet0830 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0830_ok : checkStripPacket packet0830 = true :=
  checkStripPacket_intro packet0830_shape packet0830_cache packet0830_pair

theorem packet0831_membership : packet0831 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0831_shape : checkStripShape packet0831.row = true := by
  decide +kernel

private theorem packet0831_cache : checkStripCache packet0831 = true := by
  decide +kernel

private theorem packet0831_pair (i : Fin 7) : checkEdgePair packet0831 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0831_ok : checkStripPacket packet0831 = true :=
  checkStripPacket_intro packet0831_shape packet0831_cache packet0831_pair

theorem packet0832_membership : packet0832 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0832_shape : checkStripShape packet0832.row = true := by
  decide +kernel

private theorem packet0832_cache : checkStripCache packet0832 = true := by
  decide +kernel

private theorem packet0832_pair (i : Fin 7) : checkEdgePair packet0832 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0832_ok : checkStripPacket packet0832 = true :=
  checkStripPacket_intro packet0832_shape packet0832_cache packet0832_pair

theorem packet0833_membership : packet0833 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0833_shape : checkStripShape packet0833.row = true := by
  decide +kernel

private theorem packet0833_cache : checkStripCache packet0833 = true := by
  decide +kernel

private theorem packet0833_pair (i : Fin 7) : checkEdgePair packet0833 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0833_ok : checkStripPacket packet0833 = true :=
  checkStripPacket_intro packet0833_shape packet0833_cache packet0833_pair

theorem packet0834_membership : packet0834 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0834_shape : checkStripShape packet0834.row = true := by
  decide +kernel

private theorem packet0834_cache : checkStripCache packet0834 = true := by
  decide +kernel

private theorem packet0834_pair (i : Fin 7) : checkEdgePair packet0834 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0834_ok : checkStripPacket packet0834 = true :=
  checkStripPacket_intro packet0834_shape packet0834_cache packet0834_pair

theorem packet0835_membership : packet0835 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0835_shape : checkStripShape packet0835.row = true := by
  decide +kernel

private theorem packet0835_cache : checkStripCache packet0835 = true := by
  decide +kernel

private theorem packet0835_pair (i : Fin 7) : checkEdgePair packet0835 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0835_ok : checkStripPacket packet0835 = true :=
  checkStripPacket_intro packet0835_shape packet0835_cache packet0835_pair

theorem packet0836_membership : packet0836 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0836_shape : checkStripShape packet0836.row = true := by
  decide +kernel

private theorem packet0836_cache : checkStripCache packet0836 = true := by
  decide +kernel

private theorem packet0836_pair (i : Fin 7) : checkEdgePair packet0836 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0836_ok : checkStripPacket packet0836 = true :=
  checkStripPacket_intro packet0836_shape packet0836_cache packet0836_pair

theorem packet0837_membership : packet0837 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0837_shape : checkStripShape packet0837.row = true := by
  decide +kernel

private theorem packet0837_cache : checkStripCache packet0837 = true := by
  decide +kernel

private theorem packet0837_pair (i : Fin 7) : checkEdgePair packet0837 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0837_ok : checkStripPacket packet0837 = true :=
  checkStripPacket_intro packet0837_shape packet0837_cache packet0837_pair

theorem packet0838_membership : packet0838 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0838_shape : checkStripShape packet0838.row = true := by
  decide +kernel

private theorem packet0838_cache : checkStripCache packet0838 = true := by
  decide +kernel

private theorem packet0838_pair (i : Fin 7) : checkEdgePair packet0838 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0838_ok : checkStripPacket packet0838 = true :=
  checkStripPacket_intro packet0838_shape packet0838_cache packet0838_pair

theorem packet0839_membership : packet0839 ∈ packets034 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0839_shape : checkStripShape packet0839.row = true := by
  decide +kernel

private theorem packet0839_cache : checkStripCache packet0839 = true := by
  decide +kernel

private theorem packet0839_pair (i : Fin 7) : checkEdgePair packet0839 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0839_ok : checkStripPacket packet0839 = true :=
  checkStripPacket_intro packet0839_shape packet0839_cache packet0839_pair

theorem packets034_checked : packets034.all checkStripPacket = true := by
  simp only [packets034, List.all_cons, List.all_nil, Bool.true_and, packet0816_ok,
    packet0817_ok, packet0818_ok, packet0819_ok, packet0820_ok, packet0821_ok,
    packet0822_ok, packet0823_ok, packet0824_ok, packet0825_ok, packet0826_ok,
    packet0827_ok, packet0828_ok, packet0829_ok, packet0830_ok, packet0831_ok,
    packet0832_ok, packet0833_ok, packet0834_ok, packet0835_ok, packet0836_ok,
    packet0837_ok, packet0838_ok, packet0839_ok]

theorem packets034_valid : packets034.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
