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

def packet0360 : StripRowPacket :=
  ⟨⟨⟨7,14,5,7⟩,
    ![335,1212,2503,4013,5528,6841,7771],![374,1263,2550,4050,5553,6855,7778]⟩,
    ⟨-88760345799791969346701431219,14042763237008092242228624736256⟩,
    ⟨-1155781901029063440501500905,211115206537085994983354724352⟩⟩

def packet0361 : StripRowPacket :=
  ⟨⟨⟨7,15,5,6⟩,
    ![300,1168,2465,3984,5509,6831,7768],![345,1220,2510,4019,5533,6845,7775]⟩,
    ⟨-26084925095720455475035,3676236342755726355054592⟩,
    ⟨-99598001591840763871177,15955113297083338841255936⟩⟩

def packet0362 : StripRowPacket :=
  ⟨⟨⟨7,15,5,7⟩,
    ![333,1207,2498,4008,5525,6839,7771],![372,1258,2545,4045,5550,6853,7777]⟩,
    ⟨-47142579555794165225087,7352472685511452710109184⟩,
    ⟨-11085478763364856703755,1994389162135417355156992⟩⟩

def packet0363 : StripRowPacket :=
  ⟨⟨⟨7,8,5,8⟩,
    ![384,1285,2573,4068,5565,6859,7777],![423,1340,2625,4110,5593,6875,7784]⟩,
    ⟨-98175410253188423994473,19114325421289033602318080⟩,
    ⟨-10940304908277875865091319,2525599017844933548020039680⟩⟩

def packet0364 : StripRowPacket :=
  ⟨⟨⟨7,8,5,9⟩,
    ![410,1322,2608,4095,5582,6869,7780],![445,1376,2662,4139,5612,6886,7787]⟩,
    ⟨-693435606412677202857087,152914603370312268818544640⟩,
    ⟨-4709852451662041443607803,1262799508922466774010019840⟩⟩

def packet0365 : StripRowPacket :=
  ⟨⟨⟨7,9,5,8⟩,
    ![380,1278,2567,4063,5561,6858,7777],![417,1332,2618,4104,5589,6873,7784]⟩,
    ⟨-464023203166450854382628791,88799140867463443708911972352⟩,
    ⟨-27457630836648144542179898607,6219803507079325947419148271616⟩⟩

def packet0366 : StripRowPacket :=
  ⟨⟨⟨7,9,5,9⟩,
    ![405,1315,2602,4090,5579,6867,7779],![440,1368,2655,4133,5609,6884,7787]⟩,
    ⟨-3275841580596119010972602927,710393126939707549671295778816⟩,
    ⟨-11816873787844215688516393427,3109901753539662973709574135808⟩⟩

def packet0367 : StripRowPacket :=
  ⟨⟨⟨7,8,5,10⟩,
    ![432,1357,2644,4124,5601,6878,7783],![465,1410,2699,4170,5633,6897,7791]⟩,
    ⟨-60146793079984701375839,15291460337031226881854464⟩,
    ⟨-7899104898370289909339893,2525599017844933548020039680⟩⟩

def packet0368 : StripRowPacket :=
  ⟨⟨⟨7,8,5,11⟩,
    ![452,1391,2680,4154,5622,6889,7786],![482,1443,2736,4202,5656,6909,7795]⟩,
    ⟨-509500255187016824659693,152914603370312268818544640⟩,
    ⟨-318925244670824846573209,126279950892246677401001984⟩⟩

def packet0369 : StripRowPacket :=
  ⟨⟨⟨7,9,5,10⟩,
    ![427,1351,2637,4119,5598,6877,7783],![459,1402,2691,4164,5630,6895,7790]⟩,
    ⟨-1419748767930315593442087763,355196563469853774835647889408⟩,
    ⟨-1800896755884428928353243191,565436682461756904310831661056⟩⟩

def packet0370 : StripRowPacket :=
  ⟨⟨⟨7,9,5,11⟩,
    ![447,1384,2673,4149,5618,6887,7786],![476,1435,2728,4196,5652,6907,7794]⟩,
    ⟨-343307641589306194685106875,101484732419958221381613682688⟩,
    ⟨-3996495263442251261684640837,1554950876769831486854787067904⟩⟩

def packet0371 : StripRowPacket :=
  ⟨⟨⟨7,10,5,8⟩,
    ![376,1272,2560,4058,5558,6856,7776],![413,1325,2611,4098,5585,6872,7783]⟩,
    ⟨-369300596842748610508780099,69507277677570323277439227904⟩,
    ⟨-17785028648813530824304153,3956314828641700892257386496⟩⟩

def packet0372 : StripRowPacket :=
  ⟨⟨⟨7,10,5,9⟩,
    ![401,1309,2595,4085,5576,6865,7779],![435,1361,2648,4128,5605,6882,7786]⟩,
    ⟨-2605969896347569024340322283,556058221420562586219513823232⟩,
    ⟨-7651986162628858784284373,1978157414320850446128693248⟩⟩

def packet0373 : StripRowPacket :=
  ⟨⟨⟨7,11,5,8⟩,
    ![373,1266,2554,4053,5554,6854,7775],![408,1318,2605,4093,5582,6870,7782]⟩,
    ⟨-4389668098805134365139,813043091489376498749440⟩,
    ⟨-24270259887387849684590243,5305765289164364551204986880⟩⟩

def packet0374 : StripRowPacket :=
  ⟨⟨⟨7,11,5,9⟩,
    ![398,1303,2589,4080,5572,6863,7778],![430,1354,2641,4122,5602,6880,7786]⟩,
    ⟨-340597673048943701767449,71547792051065131889950720⟩,
    ⟨-2087944584621413172432363,530576528916436455120498688⟩⟩

def packet0375 : StripRowPacket :=
  ⟨⟨⟨7,10,5,10⟩,
    ![423,1344,2631,4114,5595,6875,7782],![454,1395,2684,4159,5626,6893,7790]⟩,
    ⟨-1128767508976574582305201887,278029110710281293109756911616⟩,
    ⟨-1831845143100272044690477,565187832663100127465340928⟩⟩

def packet0376 : StripRowPacket :=
  ⟨⟨⟨7,10,5,11⟩,
    ![442,1378,2667,4144,5615,6886,7785],![471,1427,2721,4191,5649,6905,7794]⟩,
    ⟨-173554558141702664080044115,50550747401869326019955802112⟩,
    ⟨-2585464919536522764274483,989078707160425223064346624⟩⟩

def packet0377 : StripRowPacket :=
  ⟨⟨⟨7,11,5,10⟩,
    ![419,1338,2625,4109,5591,6873,7781],![449,1388,2678,4153,5623,6891,7789]⟩,
    ⟨-147452276701517789701333,35773896025532565944975360⟩,
    ⟨-17488631805040413764057017,5305765289164364551204986880⟩⟩

def packet0378 : StripRowPacket :=
  ⟨⟨⟨7,11,5,11⟩,
    ![438,1372,2661,4139,5612,6884,7785],![466,1420,2715,4186,5645,6903,7793]⟩,
    ⟨-249211433757127457037883,71547792051065131889950720⟩,
    ⟨-271111880074359534688277,102033947868545472138557440⟩⟩

def packet0379 : StripRowPacket :=
  ⟨⟨⟨7,8,5,12⟩,
    ![469,1424,2716,4185,5643,6901,7790],![498,1474,2772,4235,5680,6922,7799]⟩,
    ⟨-104383144893546658890249,38228650842578067204636160⟩,
    ⟨-4857904888462703953588467,2525599017844933548020039680⟩⟩

def packet0380 : StripRowPacket :=
  ⟨⟨⟨7,8,5,13⟩,
    ![484,1454,2752,4217,5667,6913,7794],![511,1502,2809,4270,5706,6936,7804]⟩,
    ⟨-325564903961356446462299,152914603370312268818544640⟩,
    ⟨-1668652441754455487856377,1262799508922466774010019840⟩⟩

def packet0381 : StripRowPacket :=
  ⟨⟨⟨7,9,5,12⟩,
    ![464,1417,2709,4180,5640,6899,7790],![491,1465,2765,4230,5677,6920,7798]⟩,
    ⟨-44700214690673989516075471,16145298339538807947074904064⟩,
    ⟨-12162097792809291881591451595,6219803507079325947419148271616⟩⟩

def packet0382 : StripRowPacket :=
  ⟨⟨⟨7,9,5,13⟩,
    ![479,1447,2745,4212,5663,6912,7794],![504,1494,2801,4264,5702,6934,7803]⟩,
    ⟨-1530465401654167714618893323,710393126939707549671295778816⟩,
    ⟨-4169107265924789358222169921,3109901753539662973709574135808⟩⟩

def packet0383 : StripRowPacket :=
  ⟨⟨⟨7,8,4,7⟩,
    ![497,1482,2787,4251,5691,6927,7799],![533,1553,2879,4341,5762,6969,7815]⟩,
    ⟨-116798614174263128681801,76457301685156134409272320⟩,
    ⟨-18506554600082813747583,157849938615308346751252480⟩⟩

def packets015 : List StripRowPacket :=
  [packet0360, packet0361, packet0362, packet0363, packet0364, packet0365,
   packet0366, packet0367, packet0368, packet0369, packet0370, packet0371,
   packet0372, packet0373, packet0374, packet0375, packet0376, packet0377,
   packet0378, packet0379, packet0380, packet0381, packet0382, packet0383]

theorem packet0360_membership : packet0360 ∈ packets015 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0360_shape : checkStripShape packet0360.row = true := by
  decide +kernel

private theorem packet0360_cache : checkStripCache packet0360 = true := by
  decide +kernel

private theorem packet0360_pair (i : Fin 7) : checkEdgePair packet0360 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0360_ok : checkStripPacket packet0360 = true :=
  checkStripPacket_intro packet0360_shape packet0360_cache packet0360_pair

theorem packet0361_membership : packet0361 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0361_shape : checkStripShape packet0361.row = true := by
  decide +kernel

private theorem packet0361_cache : checkStripCache packet0361 = true := by
  decide +kernel

private theorem packet0361_pair (i : Fin 7) : checkEdgePair packet0361 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0361_ok : checkStripPacket packet0361 = true :=
  checkStripPacket_intro packet0361_shape packet0361_cache packet0361_pair

theorem packet0362_membership : packet0362 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0362_shape : checkStripShape packet0362.row = true := by
  decide +kernel

private theorem packet0362_cache : checkStripCache packet0362 = true := by
  decide +kernel

private theorem packet0362_pair (i : Fin 7) : checkEdgePair packet0362 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0362_ok : checkStripPacket packet0362 = true :=
  checkStripPacket_intro packet0362_shape packet0362_cache packet0362_pair

theorem packet0363_membership : packet0363 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0363_shape : checkStripShape packet0363.row = true := by
  decide +kernel

private theorem packet0363_cache : checkStripCache packet0363 = true := by
  decide +kernel

private theorem packet0363_pair (i : Fin 7) : checkEdgePair packet0363 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0363_ok : checkStripPacket packet0363 = true :=
  checkStripPacket_intro packet0363_shape packet0363_cache packet0363_pair

theorem packet0364_membership : packet0364 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0364_shape : checkStripShape packet0364.row = true := by
  decide +kernel

private theorem packet0364_cache : checkStripCache packet0364 = true := by
  decide +kernel

private theorem packet0364_pair (i : Fin 7) : checkEdgePair packet0364 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0364_ok : checkStripPacket packet0364 = true :=
  checkStripPacket_intro packet0364_shape packet0364_cache packet0364_pair

theorem packet0365_membership : packet0365 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0365_shape : checkStripShape packet0365.row = true := by
  decide +kernel

private theorem packet0365_cache : checkStripCache packet0365 = true := by
  decide +kernel

private theorem packet0365_pair (i : Fin 7) : checkEdgePair packet0365 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0365_ok : checkStripPacket packet0365 = true :=
  checkStripPacket_intro packet0365_shape packet0365_cache packet0365_pair

theorem packet0366_membership : packet0366 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0366_shape : checkStripShape packet0366.row = true := by
  decide +kernel

private theorem packet0366_cache : checkStripCache packet0366 = true := by
  decide +kernel

private theorem packet0366_pair (i : Fin 7) : checkEdgePair packet0366 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0366_ok : checkStripPacket packet0366 = true :=
  checkStripPacket_intro packet0366_shape packet0366_cache packet0366_pair

theorem packet0367_membership : packet0367 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0367_shape : checkStripShape packet0367.row = true := by
  decide +kernel

private theorem packet0367_cache : checkStripCache packet0367 = true := by
  decide +kernel

private theorem packet0367_pair (i : Fin 7) : checkEdgePair packet0367 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0367_ok : checkStripPacket packet0367 = true :=
  checkStripPacket_intro packet0367_shape packet0367_cache packet0367_pair

theorem packet0368_membership : packet0368 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0368_shape : checkStripShape packet0368.row = true := by
  decide +kernel

private theorem packet0368_cache : checkStripCache packet0368 = true := by
  decide +kernel

private theorem packet0368_pair (i : Fin 7) : checkEdgePair packet0368 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0368_ok : checkStripPacket packet0368 = true :=
  checkStripPacket_intro packet0368_shape packet0368_cache packet0368_pair

theorem packet0369_membership : packet0369 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0369_shape : checkStripShape packet0369.row = true := by
  decide +kernel

private theorem packet0369_cache : checkStripCache packet0369 = true := by
  decide +kernel

private theorem packet0369_pair (i : Fin 7) : checkEdgePair packet0369 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0369_ok : checkStripPacket packet0369 = true :=
  checkStripPacket_intro packet0369_shape packet0369_cache packet0369_pair

theorem packet0370_membership : packet0370 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0370_shape : checkStripShape packet0370.row = true := by
  decide +kernel

private theorem packet0370_cache : checkStripCache packet0370 = true := by
  decide +kernel

private theorem packet0370_pair (i : Fin 7) : checkEdgePair packet0370 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0370_ok : checkStripPacket packet0370 = true :=
  checkStripPacket_intro packet0370_shape packet0370_cache packet0370_pair

theorem packet0371_membership : packet0371 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0371_shape : checkStripShape packet0371.row = true := by
  decide +kernel

private theorem packet0371_cache : checkStripCache packet0371 = true := by
  decide +kernel

private theorem packet0371_pair (i : Fin 7) : checkEdgePair packet0371 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0371_ok : checkStripPacket packet0371 = true :=
  checkStripPacket_intro packet0371_shape packet0371_cache packet0371_pair

theorem packet0372_membership : packet0372 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0372_shape : checkStripShape packet0372.row = true := by
  decide +kernel

private theorem packet0372_cache : checkStripCache packet0372 = true := by
  decide +kernel

private theorem packet0372_pair (i : Fin 7) : checkEdgePair packet0372 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0372_ok : checkStripPacket packet0372 = true :=
  checkStripPacket_intro packet0372_shape packet0372_cache packet0372_pair

theorem packet0373_membership : packet0373 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0373_shape : checkStripShape packet0373.row = true := by
  decide +kernel

private theorem packet0373_cache : checkStripCache packet0373 = true := by
  decide +kernel

private theorem packet0373_pair (i : Fin 7) : checkEdgePair packet0373 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0373_ok : checkStripPacket packet0373 = true :=
  checkStripPacket_intro packet0373_shape packet0373_cache packet0373_pair

theorem packet0374_membership : packet0374 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0374_shape : checkStripShape packet0374.row = true := by
  decide +kernel

private theorem packet0374_cache : checkStripCache packet0374 = true := by
  decide +kernel

private theorem packet0374_pair (i : Fin 7) : checkEdgePair packet0374 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0374_ok : checkStripPacket packet0374 = true :=
  checkStripPacket_intro packet0374_shape packet0374_cache packet0374_pair

theorem packet0375_membership : packet0375 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0375_shape : checkStripShape packet0375.row = true := by
  decide +kernel

private theorem packet0375_cache : checkStripCache packet0375 = true := by
  decide +kernel

private theorem packet0375_pair (i : Fin 7) : checkEdgePair packet0375 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0375_ok : checkStripPacket packet0375 = true :=
  checkStripPacket_intro packet0375_shape packet0375_cache packet0375_pair

theorem packet0376_membership : packet0376 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0376_shape : checkStripShape packet0376.row = true := by
  decide +kernel

private theorem packet0376_cache : checkStripCache packet0376 = true := by
  decide +kernel

private theorem packet0376_pair (i : Fin 7) : checkEdgePair packet0376 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0376_ok : checkStripPacket packet0376 = true :=
  checkStripPacket_intro packet0376_shape packet0376_cache packet0376_pair

theorem packet0377_membership : packet0377 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0377_shape : checkStripShape packet0377.row = true := by
  decide +kernel

private theorem packet0377_cache : checkStripCache packet0377 = true := by
  decide +kernel

private theorem packet0377_pair (i : Fin 7) : checkEdgePair packet0377 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0377_ok : checkStripPacket packet0377 = true :=
  checkStripPacket_intro packet0377_shape packet0377_cache packet0377_pair

theorem packet0378_membership : packet0378 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0378_shape : checkStripShape packet0378.row = true := by
  decide +kernel

private theorem packet0378_cache : checkStripCache packet0378 = true := by
  decide +kernel

private theorem packet0378_pair (i : Fin 7) : checkEdgePair packet0378 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0378_ok : checkStripPacket packet0378 = true :=
  checkStripPacket_intro packet0378_shape packet0378_cache packet0378_pair

theorem packet0379_membership : packet0379 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0379_shape : checkStripShape packet0379.row = true := by
  decide +kernel

private theorem packet0379_cache : checkStripCache packet0379 = true := by
  decide +kernel

private theorem packet0379_pair (i : Fin 7) : checkEdgePair packet0379 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0379_ok : checkStripPacket packet0379 = true :=
  checkStripPacket_intro packet0379_shape packet0379_cache packet0379_pair

theorem packet0380_membership : packet0380 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0380_shape : checkStripShape packet0380.row = true := by
  decide +kernel

private theorem packet0380_cache : checkStripCache packet0380 = true := by
  decide +kernel

private theorem packet0380_pair (i : Fin 7) : checkEdgePair packet0380 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0380_ok : checkStripPacket packet0380 = true :=
  checkStripPacket_intro packet0380_shape packet0380_cache packet0380_pair

theorem packet0381_membership : packet0381 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0381_shape : checkStripShape packet0381.row = true := by
  decide +kernel

private theorem packet0381_cache : checkStripCache packet0381 = true := by
  decide +kernel

private theorem packet0381_pair (i : Fin 7) : checkEdgePair packet0381 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0381_ok : checkStripPacket packet0381 = true :=
  checkStripPacket_intro packet0381_shape packet0381_cache packet0381_pair

theorem packet0382_membership : packet0382 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0382_shape : checkStripShape packet0382.row = true := by
  decide +kernel

private theorem packet0382_cache : checkStripCache packet0382 = true := by
  decide +kernel

private theorem packet0382_pair (i : Fin 7) : checkEdgePair packet0382 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0382_ok : checkStripPacket packet0382 = true :=
  checkStripPacket_intro packet0382_shape packet0382_cache packet0382_pair

theorem packet0383_membership : packet0383 ∈ packets015 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0383_shape : checkStripShape packet0383.row = true := by
  decide +kernel

private theorem packet0383_cache : checkStripCache packet0383 = true := by
  decide +kernel

private theorem packet0383_pair (i : Fin 7) : checkEdgePair packet0383 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0383_ok : checkStripPacket packet0383 = true :=
  checkStripPacket_intro packet0383_shape packet0383_cache packet0383_pair

theorem packets015_checked : packets015.all checkStripPacket = true := by
  simp only [packets015, List.all_cons, List.all_nil, Bool.true_and, packet0360_ok,
    packet0361_ok, packet0362_ok, packet0363_ok, packet0364_ok, packet0365_ok,
    packet0366_ok, packet0367_ok, packet0368_ok, packet0369_ok, packet0370_ok,
    packet0371_ok, packet0372_ok, packet0373_ok, packet0374_ok, packet0375_ok,
    packet0376_ok, packet0377_ok, packet0378_ok, packet0379_ok, packet0380_ok,
    packet0381_ok, packet0382_ok, packet0383_ok]

theorem packets015_valid : packets015.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
