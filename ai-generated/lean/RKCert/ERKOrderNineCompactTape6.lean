module

public import RKCert.ERKCompactResidueCore

@[expose] public section

namespace RKCert.CompactResidue.Tape6
set_option maxHeartbeats 0

def rel : List Nat := [479,1079,183,407,799,245,546,394,999]

def t0 : Term := .raw []
private theorem c0 : Value 1319 rel t0 [] := .raw []
def t1 : Term := .raw [1]
private theorem c1 : Value 1319 rel t1 [1] := .raw [1]
def t2 : Term := .raw [163,815,731,520,651,895,160,1101,1124]
private theorem c2 : Value 1319 rel t2 [163,815,731,520,651,895,160,1101,1124] := .raw [163,815,731,520,651,895,160,1101,1124]
def t3 : Term := .raw [371,1159,934,803,1137,1086,171,82,949]
private theorem c3 : Value 1319 rel t3 [371,1159,934,803,1137,1086,171,82,949] := .raw [371,1159,934,803,1137,1086,171,82,949]
def t4 : Term := .raw [817,875,292,492,355,648,870,845,1293]
private theorem c4 : Value 1319 rel t4 [817,875,292,492,355,648,870,845,1293] := .raw [817,875,292,492,355,648,870,845,1293]
def t5 : Term := .raw [1289,1107,681,823,495,9,118,610,591]
private theorem c5 : Value 1319 rel t5 [1289,1107,681,823,495,9,118,610,591] := .raw [1289,1107,681,823,495,9,118,610,591]
def t6 : Term := .raw [0,1]
private theorem c6 : Value 1319 rel t6 [0,1] := .raw [0,1]
def t7 : Term := .raw [581]
private theorem c7 : Value 1319 rel t7 [581] := .raw [581]
def t8 : Term := .raw [6]
private theorem c8 : Value 1319 rel t8 [6] := .raw [6]
def t9 : Term := .mul t8 t6
private theorem c9 : Value 1319 rel t9 [0,6] :=
  .mul [] c8 c6 (of_decide_eq_true rfl)
def t10 : Term := .raw [2]
private theorem c10 : Value 1319 rel t10 [2] := .raw [2]
def t11 : Term := .neg t9
private theorem c11 : Value 1319 rel t11 [0,1313] :=
  .neg c9 (of_decide_eq_true rfl)
def t12 : Term := .add t10 t11
private theorem c12 : Value 1319 rel t12 [2,1313] :=
  .add c10 c11 (of_decide_eq_true rfl)
def t13 : Term := .mul t12 t7
private theorem c13 : Value 1319 rel t13 [1162,471] :=
  .mul [] c12 c7 (of_decide_eq_true rfl)
def t14 : Term := .raw [54]
private theorem c14 : Value 1319 rel t14 [54] := .raw [54]
def t15 : Term := .mul t14 t6
private theorem c15 : Value 1319 rel t15 [0,54] :=
  .mul [] c14 c6 (of_decide_eq_true rfl)
def t16 : Term := .raw [28]
private theorem c16 : Value 1319 rel t16 [28] := .raw [28]
def t17 : Term := .neg t16
private theorem c17 : Value 1319 rel t17 [1291] :=
  .neg c16 (of_decide_eq_true rfl)
def t18 : Term := .add t17 t15
private theorem c18 : Value 1319 rel t18 [1291,54] :=
  .add c17 c15 (of_decide_eq_true rfl)
def t19 : Term := .mul t18 t7
private theorem c19 : Value 1319 rel t19 [879,1037] :=
  .mul [] c18 c7 (of_decide_eq_true rfl)
def t20 : Term := .raw [126]
private theorem c20 : Value 1319 rel t20 [126] := .raw [126]
def t21 : Term := .mul t20 t6
private theorem c21 : Value 1319 rel t21 [0,126] :=
  .mul [] c20 c6 (of_decide_eq_true rfl)
def t22 : Term := .raw [112]
private theorem c22 : Value 1319 rel t22 [112] := .raw [112]
def t23 : Term := .neg t21
private theorem c23 : Value 1319 rel t23 [0,1193] :=
  .neg c21 (of_decide_eq_true rfl)
def t24 : Term := .add t22 t23
private theorem c24 : Value 1319 rel t24 [112,1193] :=
  .add c22 c23 (of_decide_eq_true rfl)
def t25 : Term := .mul t24 t7
private theorem c25 : Value 1319 rel t25 [441,658] :=
  .mul [] c24 c7 (of_decide_eq_true rfl)
def t26 : Term := .neg t10
private theorem c26 : Value 1319 rel t26 [1317] :=
  .neg c10 (of_decide_eq_true rfl)
def t27 : Term := .add t6 t26
private theorem c27 : Value 1319 rel t27 [1317,1] :=
  .add c6 c26 (of_decide_eq_true rfl)
def t28 : Term := .neg t2
private theorem c28 : Value 1319 rel t28 [1156,504,588,799,668,424,1159,218,195] :=
  .neg c2 (of_decide_eq_true rfl)
def t29 : Term := .neg t3
private theorem c29 : Value 1319 rel t29 [948,160,385,516,182,233,1148,1237,370] :=
  .neg c3 (of_decide_eq_true rfl)
def t30 : Term := .neg t4
private theorem c30 : Value 1319 rel t30 [502,444,1027,827,964,671,449,474,26] :=
  .neg c4 (of_decide_eq_true rfl)
def t31 : Term := .neg t5
private theorem c31 : Value 1319 rel t31 [30,212,638,496,824,1310,1201,709,728] :=
  .neg c5 (of_decide_eq_true rfl)
def t32 : Term := .mul t30 t31
private theorem c32 : Value 1319 rel t32 [788,497,793,1100,551,1209,721,1129,150] :=
  .mul [1135,708,81,985,667,1293,669,462] c30 c31 (of_decide_eq_true rfl)
def t33 : Term := .add t30 t31
private theorem c33 : Value 1319 rel t33 [532,656,346,4,469,662,331,1183,754] :=
  .add c30 c31 (of_decide_eq_true rfl)
def t34 : Term := .mul t29 t32
private theorem c34 : Value 1319 rel t34 [273,325,528,339,256,899,279,710,773] :=
  .mul [498,617,827,816,988,311,832,102] c29 c32 (of_decide_eq_true rfl)
def t35 : Term := .mul t29 t33
private theorem c35 : Value 1319 rel t35 [1273,857,1273,253,141,1268,28,797,797] :=
  .mul [635,17,640,209,1090,1046,244,671] c29 c33 (of_decide_eq_true rfl)
def t36 : Term := .add t35 t32
private theorem c36 : Value 1319 rel t36 [742,35,747,34,692,1158,749,607,947] :=
  .add c35 c32 (of_decide_eq_true rfl)
def t37 : Term := .add t29 t33
private theorem c37 : Value 1319 rel t37 [161,816,731,520,651,895,160,1101,1124] :=
  .add c29 c33 (of_decide_eq_true rfl)
def t38 : Term := .mul t28 t34
private theorem c38 : Value 1319 rel t38 [1162,471] :=
  .mul [792,480,564,1169,397,361,267,369] c28 c34 (of_decide_eq_true rfl)
def t39 : Term := .mul t28 t36
private theorem c39 : Value 1319 rel t39 [606,712,791,980,1063,420,1040,609,546] :=
  .mul [810,192,1229,139,890,115,56,5] c28 c36 (of_decide_eq_true rfl)
def t40 : Term := .mul t28 t37
private theorem c40 : Value 1319 rel t40 [1018,623,572,1285,627,161,570,712,372] :=
  .mul [123,17,287,599,702,970,940,226] c28 c37 (of_decide_eq_true rfl)
def t41 : Term := .add t39 t34
private theorem c41 : Value 1319 rel t41 [879,1037] :=
  .add c39 c34 (of_decide_eq_true rfl)
def t42 : Term := .add t40 t36
private theorem c42 : Value 1319 rel t42 [441,658] :=
  .add c40 c36 (of_decide_eq_true rfl)
def t43 : Term := .add t28 t37
private theorem c43 : Value 1319 rel t43 [1317,1] :=
  .add c28 c37 (of_decide_eq_true rfl)
def t44 : Term := .add t1 t29
private theorem c44 : Value 1319 rel t44 [949,160,385,516,182,233,1148,1237,370] :=
  .add c1 c29 (of_decide_eq_true rfl)
def t45 : Term := .mul t10 t3
private theorem c45 : Value 1319 rel t45 [742,999,549,287,955,853,342,164,579] :=
  .mul [] c10 c3 (of_decide_eq_true rfl)
def t46 : Term := .raw [3]
private theorem c46 : Value 1319 rel t46 [3] := .raw [3]
def t47 : Term := .mul t46 t4
private theorem c47 : Value 1319 rel t47 [1132,1306,876,157,1065,625,1291,1216,1241] :=
  .mul [] c46 c4 (of_decide_eq_true rfl)
def t48 : Term := .neg t47
private theorem c48 : Value 1319 rel t48 [187,13,443,1162,254,694,28,103,78] :=
  .neg c47 (of_decide_eq_true rfl)
def t49 : Term := .add t45 t48
private theorem c49 : Value 1319 rel t49 [929,1012,992,130,1209,228,370,267,657] :=
  .add c45 c48 (of_decide_eq_true rfl)
def t50 : Term := .add t49 t1
private theorem c50 : Value 1319 rel t50 [930,1012,992,130,1209,228,370,267,657] :=
  .add c49 c1 (of_decide_eq_true rfl)
def t51 : Term := .mul t44 t50
private theorem c51 : Value 1319 rel t51 [808,208,1232,121,1198,603,902,630,1007] :=
  .mul [676,656,1092,350,1233,985,614,394] c44 c50 (of_decide_eq_true rfl)
def t52 : Term := .mul t4 t4
private theorem c52 : Value 1319 rel t52 [529,691,747,711,636,322,549,118,388] :=
  .mul [794,1253,521,1059,3,179,902,676] c4 c4 (of_decide_eq_true rfl)
def t53 : Term := .mul t52 t4
private theorem c53 : Value 1319 rel t53 [570,1306,788,727,541,460,416,883,685] :=
  .mul [864,780,395,191,1292,776,885,464] c52 c4 (of_decide_eq_true rfl)
def t54 : Term := .neg t20
private theorem c54 : Value 1319 rel t54 [1193] :=
  .neg c20 (of_decide_eq_true rfl)
def t55 : Term := .mul t54 t52
private theorem c55 : Value 1319 rel t55 [615,1307,846,106,323,317,733,960,1234] :=
  .mul [] c54 c52 (of_decide_eq_true rfl)
def t56 : Term := .mul t14 t4
private theorem c56 : Value 1319 rel t56 [591,1085,1259,188,704,698,815,784,1234] :=
  .mul [] c14 c4 (of_decide_eq_true rfl)
def t57 : Term := .add t55 t56
private theorem c57 : Value 1319 rel t57 [1206,1073,786,294,1027,1015,229,425,1149] :=
  .add c55 c56 (of_decide_eq_true rfl)
def t58 : Term := .neg t8
private theorem c58 : Value 1319 rel t58 [1313] :=
  .neg c8 (of_decide_eq_true rfl)
def t59 : Term := .add t57 t58
private theorem c59 : Value 1319 rel t59 [1200,1073,786,294,1027,1015,229,425,1149] :=
  .add c57 c58 (of_decide_eq_true rfl)
def t60 : Term := .mul t59 t7
private theorem c60 : Value 1319 rel t60 [768,845,292,663,499,122,1149,272,155] :=
  .mul [] c59 c7 (of_decide_eq_true rfl)
def t61 : Term := .add t53 t60
private theorem c61 : Value 1319 rel t61 [19,832,1080,71,1040,582,246,1155,840] :=
  .add c53 c60 (of_decide_eq_true rfl)
def t62 : Term := .mul t51 t61
private theorem c62 : Value 1319 rel t62 [600,749,1041,1040,1303,662,325,107,345] :=
  .mul [5,16,731,560,465,289,950,401] c51 c61 (of_decide_eq_true rfl)
def t63 : Term := .mul t2 t2
private theorem c63 : Value 1319 rel t63 [383,209,147,568,318,1269,1124,339,368] :=
  .mul [72,1302,1032,720,617,349,379,1093] c2 c2 (of_decide_eq_true rfl)
def t64 : Term := .mul t46 t63
private theorem c64 : Value 1319 rel t64 [1149,627,441,385,954,1169,734,1017,1104] :=
  .mul [] c46 c63 (of_decide_eq_true rfl)
def t65 : Term := .mul t3 t3
private theorem c65 : Value 1319 rel t65 [97,314,1112,1183,1272,213,1142,945,222] :=
  .mul [13,1183,731,569,212,41,1260,1043] c3 c3 (of_decide_eq_true rfl)
def t66 : Term := .mul t8 t65
private theorem c66 : Value 1319 rel t66 [582,565,77,503,1037,1278,257,394,13] :=
  .mul [] c8 c65 (of_decide_eq_true rfl)
def t67 : Term := .neg t66
private theorem c67 : Value 1319 rel t67 [737,754,1242,816,282,41,1062,925,1306] :=
  .neg c66 (of_decide_eq_true rfl)
def t68 : Term := .add t64 t67
private theorem c68 : Value 1319 rel t68 [567,62,364,1201,1236,1210,477,623,1091] :=
  .add c64 c67 (of_decide_eq_true rfl)
def t69 : Term := .mul t62 t68
private theorem c69 : Value 1319 rel t69 [648,748,759,1016,984,700,900,748,624] :=
  .mul [1271,335,757,743,562,1066,7,480] c62 c68 (of_decide_eq_true rfl)
def t70 : Term := .add t1 t30
private theorem c70 : Value 1319 rel t70 [503,444,1027,827,964,671,449,474,26] :=
  .add c1 c30 (of_decide_eq_true rfl)
def t71 : Term := .mul t70 t70
private theorem c71 : Value 1319 rel t71 [215,260,163,1046,1245,345,128,1066,440] :=
  .mul [794,1253,521,1059,3,179,902,676] c70 c70 (of_decide_eq_true rfl)
def t72 : Term := .mul t65 t3
private theorem c72 : Value 1319 rel t72 [639,25,1204,484,1279,682,1097,622,833] :=
  .mul [1091,1173,1004,483,53,1050,710,957] c65 c3 (of_decide_eq_true rfl)
def t73 : Term := .mul t54 t65
private theorem c73 : Value 1319 rel t73 [968,6,1021,1308,646,861,1198,959,1046] :=
  .mul [] c54 c65 (of_decide_eq_true rfl)
def t74 : Term := .mul t14 t3
private theorem c74 : Value 1319 rel t74 [249,593,314,1154,724,608,1,471,1124] :=
  .mul [] c14 c3 (of_decide_eq_true rfl)
def t75 : Term := .add t73 t74
private theorem c75 : Value 1319 rel t75 [1217,599,16,1143,51,150,1199,111,851] :=
  .add c73 c74 (of_decide_eq_true rfl)
def t76 : Term := .add t75 t58
private theorem c76 : Value 1319 rel t76 [1211,599,16,1143,51,150,1199,111,851] :=
  .add c75 c58 (of_decide_eq_true rfl)
def t77 : Term := .mul t76 t7
private theorem c77 : Value 1319 rel t77 [564,1122,63,626,613,96,187,1179,1125] :=
  .mul [] c76 c7 (of_decide_eq_true rfl)
def t78 : Term := .add t72 t77
private theorem c78 : Value 1319 rel t78 [1203,1147,1267,1110,573,778,1284,482,639] :=
  .add c72 c77 (of_decide_eq_true rfl)
def t79 : Term := .mul t71 t78
private theorem c79 : Value 1319 rel t79 [107,206,1181,1283,1101,160,1305,1097,313] :=
  .mul [22,438,601,436,70,95,719,213] c71 c78 (of_decide_eq_true rfl)
def t80 : Term := .mul t8 t52
private theorem c80 : Value 1319 rel t80 [536,189,525,309,1178,613,656,708,1009] :=
  .mul [] c8 c52 (of_decide_eq_true rfl)
def t81 : Term := .neg t80
private theorem c81 : Value 1319 rel t81 [783,1130,794,1010,141,706,663,611,310] :=
  .neg c80 (of_decide_eq_true rfl)
def t82 : Term := .add t64 t81
private theorem c82 : Value 1319 rel t82 [613,438,1235,76,1095,556,78,309,95] :=
  .add c64 c81 (of_decide_eq_true rfl)
def t83 : Term := .mul t79 t82
private theorem c83 : Value 1319 rel t83 [203,511,973,1277,272,855,847,482,218] :=
  .mul [59,1057,1009,1058,803,1239,510,717] c79 c82 (of_decide_eq_true rfl)
def t84 : Term := .neg t83
private theorem c84 : Value 1319 rel t84 [1116,808,346,42,1047,464,472,837,1101] :=
  .neg c83 (of_decide_eq_true rfl)
def t85 : Term := .add t69 t84
private theorem c85 : Value 1319 rel t85 [445,237,1105,1058,712,1164,53,266,406] :=
  .add c69 c84 (of_decide_eq_true rfl)
def t86 : Term := .mul t46 t2
private theorem c86 : Value 1319 rel t86 [489,1126,874,241,634,47,480,665,734] :=
  .mul [] c46 c2 (of_decide_eq_true rfl)
def t87 : Term := .mul t86 t3
private theorem c87 : Value 1319 rel t87 [887,1047,252,1018,696,217,173,780,683] :=
  .mul [485,357,1163,304,51,696,764,134] c86 c3 (of_decide_eq_true rfl)
def t88 : Term := .raw [4]
private theorem c88 : Value 1319 rel t88 [4] := .raw [4]
def t89 : Term := .mul t88 t65
private theorem c89 : Value 1319 rel t89 [388,1256,491,775,1131,852,611,1142,888] :=
  .mul [] c88 c65 (of_decide_eq_true rfl)
def t90 : Term := .neg t89
private theorem c90 : Value 1319 rel t90 [931,63,828,544,188,467,708,177,431] :=
  .neg c89 (of_decide_eq_true rfl)
def t91 : Term := .add t87 t90
private theorem c91 : Value 1319 rel t91 [499,1110,1080,243,884,684,881,957,1114] :=
  .add c87 c90 (of_decide_eq_true rfl)
def t92 : Term := .mul t62 t91
private theorem c92 : Value 1319 rel t92 [156,924,344,973,49,1064,1042,755,30] :=
  .mul [865,27,550,151,802,76,182,501] c62 c91 (of_decide_eq_true rfl)
def t93 : Term := .mul t86 t4
private theorem c93 : Value 1319 rel t93 [938,636,107,168,347,944,816,736,648] :=
  .mul [184,328,916,294,290,1112,67,701] c86 c4 (of_decide_eq_true rfl)
def t94 : Term := .mul t88 t52
private theorem c94 : Value 1319 rel t94 [797,126,350,206,1225,1288,877,472,233] :=
  .mul [] c88 c52 (of_decide_eq_true rfl)
def t95 : Term := .neg t94
private theorem c95 : Value 1319 rel t95 [522,1193,969,1113,94,31,442,847,1086] :=
  .neg c94 (of_decide_eq_true rfl)
def t96 : Term := .add t93 t95
private theorem c96 : Value 1319 rel t96 [141,510,1076,1281,441,975,1258,264,415] :=
  .add c93 c95 (of_decide_eq_true rfl)
def t97 : Term := .mul t79 t96
private theorem c97 : Value 1319 rel t97 [25,154,1002,1179,197,1146,1137,976,390] :=
  .mul [869,1079,1185,1137,835,983,301,633] c79 c96 (of_decide_eq_true rfl)
def t98 : Term := .neg t97
private theorem c98 : Value 1319 rel t98 [1294,1165,317,140,1122,173,182,343,929] :=
  .neg c97 (of_decide_eq_true rfl)
def t99 : Term := .add t92 t98
private theorem c99 : Value 1319 rel t99 [131,770,661,1113,1171,1237,1224,1098,959] :=
  .add c92 c98 (of_decide_eq_true rfl)
def t100 : Term := .mul t64 t99
private theorem c100 : Value 1319 rel t100 [52,1241,41,119,938,1116,166,790,871] :=
  .mul [724,167,246,911,1048,1284,775,898] c64 c99 (of_decide_eq_true rfl)
def t101 : Term := .neg t86
private theorem c101 : Value 1319 rel t101 [830,193,445,1078,685,1272,839,654,585] :=
  .neg c86 (of_decide_eq_true rfl)
def t102 : Term := .mul t101 t85
private theorem c102 : Value 1319 rel t102 [997,812,723,940,710,1228,830,207,254] :=
  .mul [930,1048,818,1143,710,200,591,90] c101 c85 (of_decide_eq_true rfl)
def t103 : Term := .mul t88 t85
private theorem c103 : Value 1319 rel t103 [461,948,463,275,210,699,212,1064,305] :=
  .mul [] c88 c85 (of_decide_eq_true rfl)
def t104 : Term := .mul t8 t99
private theorem c104 : Value 1319 rel t104 [786,663,9,83,431,827,749,1312,478] :=
  .mul [] c8 c99 (of_decide_eq_true rfl)
def t105 : Term := .neg t104
private theorem c105 : Value 1319 rel t105 [533,656,1310,1236,888,492,570,7,841] :=
  .neg c104 (of_decide_eq_true rfl)
def t106 : Term := .add t103 t105
private theorem c106 : Value 1319 rel t106 [994,285,454,192,1098,1191,782,1071,1146] :=
  .add c103 c105 (of_decide_eq_true rfl)
def t107 : Term := .raw [5]
private theorem c107 : Value 1319 rel t107 [5] := .raw [5]
def t108 : Term := .mul t107 t3
private theorem c108 : Value 1319 rel t108 [536,519,713,58,409,154,855,410,788] :=
  .mul [] c107 c3 (of_decide_eq_true rfl)
def t109 : Term := .mul t108 t4
private theorem c109 : Value 1319 rel t109 [1178,759,827,870,401,507,142,814,267] :=
  .mul [1170,640,1179,1161,1003,899,387,616] c108 c4 (of_decide_eq_true rfl)
def t110 : Term := .neg t109
private theorem c110 : Value 1319 rel t110 [141,560,492,449,918,812,1177,505,1052] :=
  .neg c109 (of_decide_eq_true rfl)
def t111 : Term := .add t89 t110
private theorem c111 : Value 1319 rel t111 [529,497,983,1224,730,345,469,328,621] :=
  .add c89 c110 (of_decide_eq_true rfl)
def t112 : Term := .mul t10 t4
private theorem c112 : Value 1319 rel t112 [315,431,584,984,710,1296,421,371,1267] :=
  .mul [] c10 c4 (of_decide_eq_true rfl)
def t113 : Term := .add t111 t112
private theorem c113 : Value 1319 rel t113 [844,928,248,889,121,322,890,699,569] :=
  .add c111 c112 (of_decide_eq_true rfl)
def t114 : Term := .neg t1
private theorem c114 : Value 1319 rel t114 [1318] :=
  .neg c1 (of_decide_eq_true rfl)
def t115 : Term := .add t113 t114
private theorem c115 : Value 1319 rel t115 [843,928,248,889,121,322,890,699,569] :=
  .add c113 c114 (of_decide_eq_true rfl)
def t116 : Term := .neg t115
private theorem c116 : Value 1319 rel t116 [476,391,1071,430,1198,997,429,620,750] :=
  .neg c115 (of_decide_eq_true rfl)
def t117 : Term := .add t3 t30
private theorem c117 : Value 1319 rel t117 [873,284,642,311,782,438,620,556,975] :=
  .add c3 c30 (of_decide_eq_true rfl)
def t118 : Term := .mul t46 t117
private theorem c118 : Value 1319 rel t118 [1300,852,607,933,1027,1314,541,349,287] :=
  .mul [] c46 c117 (of_decide_eq_true rfl)
def t119 : Term := .mul t26 t2
private theorem c119 : Value 1319 rel t119 [993,1008,1176,279,17,848,999,436,390] :=
  .mul [] c26 c2 (of_decide_eq_true rfl)
def t120 : Term := .mul t116 t63
private theorem c120 : Value 1319 rel t120 [846,1106,484,482,1139,322,210,1040,1029] :=
  .mul [439,1255,1123,939,265,879,1215,329] c116 c63 (of_decide_eq_true rfl)
def t121 : Term := .mul t116 t119
private theorem c121 : Value 1319 rel t121 [849,622,608,1059,85,1231,983,298,756] :=
  .mul [1094,483,807,902,75,789,508,1001] c116 c119 (of_decide_eq_true rfl)
def t122 : Term := .mul t118 t63
private theorem c122 : Value 1319 rel t122 [975,542,573,310,704,1231,23,234,1029] :=
  .mul [411,396,78,1178,432,135,1112,96] c118 c63 (of_decide_eq_true rfl)
def t123 : Term := .mul t118 t119
private theorem c123 : Value 1319 rel t123 [102,497,1029,938,621,135,1286,1231,1249] :=
  .mul [717,1261,825,1299,478,832,1244,1134] c118 c119 (of_decide_eq_true rfl)
def t124 : Term := .add t121 t122
private theorem c124 : Value 1319 rel t124 [505,1164,1181,50,789,1143,1006,532,466] :=
  .add c121 c122 (of_decide_eq_true rfl)
def t125 : Term := .add t116 t123
private theorem c125 : Value 1319 rel t125 [578,888,781,49,500,1132,396,532,680] :=
  .add c116 c123 (of_decide_eq_true rfl)
def t126 : Term := .raw [42]
private theorem c126 : Value 1319 rel t126 [42] := .raw [42]
def t127 : Term := .mul t126 t7
private theorem c127 : Value 1319 rel t127 [660] :=
  .mul [] c126 c7 (of_decide_eq_true rfl)
def t128 : Term := .mul t127 t100
private theorem c128 : Value 1319 rel t128 [26,1280,680,719,469,558,83,395,1095] :=
  .mul [] c127 c100 (of_decide_eq_true rfl)
def t129 : Term := .mul t16 t7
private theorem c129 : Value 1319 rel t129 [440] :=
  .mul [] c16 c7 (of_decide_eq_true rfl)
def t130 : Term := .mul t129 t102
private theorem c130 : Value 1319 rel t130 [772,1150,241,753,1116,849,1156,69,964] :=
  .mul [] c129 c102 (of_decide_eq_true rfl)
def t131 : Term := .raw [21]
private theorem c131 : Value 1319 rel t131 [21] := .raw [21]
def t132 : Term := .mul t131 t7
private theorem c132 : Value 1319 rel t132 [330] :=
  .mul [] c131 c7 (of_decide_eq_true rfl)
def t133 : Term := .mul t132 t106
private theorem c133 : Value 1319 rel t133 [908,401,773,48,934,1287,855,1257,946] :=
  .mul [] c132 c106 (of_decide_eq_true rfl)
def t134 : Term := .mul t116 t128
private theorem c134 : Value 1319 rel t134 [1070,1118,441,780,1252,37,548,45,807] :=
  .mul [808,455,226,1232,150,363,607,832] c116 c128 (of_decide_eq_true rfl)
def t135 : Term := .mul t116 t130
private theorem c135 : Value 1319 rel t135 [64,627,1035,14,870,76,19,1235,820] :=
  .mul [764,580,266,533,265,1065,996,188] c116 c130 (of_decide_eq_true rfl)
def t136 : Term := .mul t116 t133
private theorem c136 : Value 1319 rel t136 [1236,479,1300,275,488,503,226,308,807] :=
  .mul [1160,734,296,130,483,859,19,1197] c116 c133 (of_decide_eq_true rfl)
def t137 : Term := .mul t118 t128
private theorem c137 : Value 1319 rel t137 [628,115,938,613,1055,1197,115,486,970] :=
  .mul [498,604,197,62,227,898,612,343] c118 c128 (of_decide_eq_true rfl)
def t138 : Term := .mul t118 t130
private theorem c138 : Value 1319 rel t138 [624,542,101,169,471,223,936,487,863] :=
  .mul [277,225,859,434,832,293,267,997] c118 c130 (of_decide_eq_true rfl)
def t139 : Term := .mul t118 t133
private theorem c139 : Value 1319 rel t139 [777,1129,635,839,472,1067,455,929,435] :=
  .mul [1252,534,163,216,1261,979,328,1107] c118 c133 (of_decide_eq_true rfl)
def t140 : Term := .add t135 t137
private theorem c140 : Value 1319 rel t140 [692,742,654,627,606,1273,134,402,471] :=
  .add c135 c137 (of_decide_eq_true rfl)
def t141 : Term := .add t136 t138
private theorem c141 : Value 1319 rel t141 [541,1021,82,444,959,726,1162,795,351] :=
  .add c136 c138 (of_decide_eq_true rfl)
def t142 : Term := .mul t106 t120
private theorem c142 : Value 1319 rel t142 [1134,1065,143,261,293,165,833,65,1113] :=
  .mul [670,1166,114,1021,1292,589,626,48] c106 c120 (of_decide_eq_true rfl)
def t143 : Term := .mul t106 t124
private theorem c143 : Value 1319 rel t143 [516,1088,397,835,913,1147,1314,204,972] :=
  .mul [933,736,26,246,509,411,237,1160] c106 c124 (of_decide_eq_true rfl)
def t144 : Term := .mul t106 t125
private theorem c144 : Value 1319 rel t144 [1043,896,603,435,391,213,352,350,764] :=
  .mul [320,944,965,919,454,1177,1026,1070] c106 c125 (of_decide_eq_true rfl)
def t145 : Term := .mul t106 t118
private theorem c145 : Value 1319 rel t145 [470,559,1221,718,569,311,501,1078,421] :=
  .mul [1051,817,652,864,1087,1278,1312,471] c106 c118 (of_decide_eq_true rfl)
def t146 : Term := .mul t118 t100
private theorem c146 : Value 1319 rel t146 [1256,230,557,1226,791,1075,230,972,621] :=
  .mul [996,1208,394,124,454,477,1224,686] c118 c100 (of_decide_eq_true rfl)
def t147 : Term := .mul t118 t102
private theorem c147 : Value 1319 rel t147 [553,307,303,507,94,669,170,142,1270] :=
  .mul [831,675,1258,1302,1177,879,801,353] c118 c102 (of_decide_eq_true rfl)
def t148 : Term := .mul t118 t106
private theorem c148 : Value 1319 rel t148 [470,559,1221,718,569,311,501,1078,421] :=
  .mul [1051,817,652,864,1087,1278,1312,471] c118 c106 (of_decide_eq_true rfl)
def t149 : Term := .neg t146
private theorem c149 : Value 1319 rel t149 [63,1089,762,93,528,244,1089,347,698] :=
  .neg c146 (of_decide_eq_true rfl)
def t150 : Term := .neg t147
private theorem c150 : Value 1319 rel t150 [766,1012,1016,812,1225,650,1149,1177,49] :=
  .neg c147 (of_decide_eq_true rfl)
def t151 : Term := .neg t148
private theorem c151 : Value 1319 rel t151 [849,760,98,601,750,1008,818,241,898] :=
  .neg c148 (of_decide_eq_true rfl)
def t152 : Term := .add t143 t149
private theorem c152 : Value 1319 rel t152 [579,858,1159,928,122,72,1084,551,351] :=
  .add c143 c149 (of_decide_eq_true rfl)
def t153 : Term := .add t144 t150
private theorem c153 : Value 1319 rel t153 [490,589,300,1247,297,863,182,208,813] :=
  .add c144 c150 (of_decide_eq_true rfl)
def t154 : Term := .add t145 t151
private theorem c154 : Value 1319 rel t154 [] :=
  .add c145 c151 (of_decide_eq_true rfl)
def t155 : Term := .mul t106 t142
private theorem c155 : Value 1319 rel t155 [834,506,1201,802,635,130,768,131,306] :=
  .mul [1030,744,576,474,666,647,187,25] c106 c142 (of_decide_eq_true rfl)
def t156 : Term := .mul t106 t152
private theorem c156 : Value 1319 rel t156 [1049,1161,686,607,1060,734,38,232,1130] :=
  .mul [742,1102,223,16,201,344,822,1270] c106 c152 (of_decide_eq_true rfl)
def t157 : Term := .mul t106 t153
private theorem c157 : Value 1319 rel t157 [1181,760,54,147,471,65,1,1305,1244] :=
  .mul [200,108,881,182,255,456,574,484] c106 c153 (of_decide_eq_true rfl)
def t158 : Term := .mul t106 t154
private theorem c158 : Value 1319 rel t158 [] :=
  .mul [] c106 c154 (of_decide_eq_true rfl)
def t159 : Term := .mul t153 t100
private theorem c159 : Value 1319 rel t159 [581,251,455,438,1059,1056,185,768,881] :=
  .mul [876,615,318,21,1102,546,1265,1139] c153 c100 (of_decide_eq_true rfl)
def t160 : Term := .mul t153 t102
private theorem c160 : Value 1319 rel t160 [669,846,1175,98,990,1271,624,817,246] :=
  .mul [865,967,1192,891,201,1093,791,738] c153 c102 (of_decide_eq_true rfl)
def t161 : Term := .mul t153 t106
private theorem c161 : Value 1319 rel t161 [1181,760,54,147,471,65,1,1305,1244] :=
  .mul [200,108,881,182,255,456,574,484] c153 c106 (of_decide_eq_true rfl)
def t162 : Term := .neg t159
private theorem c162 : Value 1319 rel t162 [738,1068,864,881,260,263,1134,551,438] :=
  .neg c159 (of_decide_eq_true rfl)
def t163 : Term := .neg t160
private theorem c163 : Value 1319 rel t163 [650,473,144,1221,329,48,695,502,1073] :=
  .neg c160 (of_decide_eq_true rfl)
def t164 : Term := .neg t161
private theorem c164 : Value 1319 rel t164 [138,559,1265,1172,848,1254,1318,14,75] :=
  .neg c161 (of_decide_eq_true rfl)
def t165 : Term := .add t155 t162
private theorem c165 : Value 1319 rel t165 [253,255,746,364,895,393,583,682,744] :=
  .add c155 c162 (of_decide_eq_true rfl)
def t166 : Term := .add t156 t163
private theorem c166 : Value 1319 rel t166 [380,315,830,509,70,782,733,734,884] :=
  .add c156 c163 (of_decide_eq_true rfl)
def t167 : Term := .add t157 t164
private theorem c167 : Value 1319 rel t167 [] :=
  .add c157 c164 (of_decide_eq_true rfl)
def t168 : Term := .mul t106 t165
private theorem c168 : Value 1319 rel t168 [499,251,766,439,905,880,504,339,495] :=
  .mul [963,1249,85,590,264,201,299,550] c106 c165 (of_decide_eq_true rfl)
def t169 : Term := .mul t106 t166
private theorem c169 : Value 1319 rel t169 [375,467,219,267,1126,615,821,358,269] :=
  .mul [1305,290,979,495,497,590,66,72] c106 c166 (of_decide_eq_true rfl)
def t170 : Term := .mul t106 t167
private theorem c170 : Value 1319 rel t170 [] :=
  .mul [] c106 c167 (of_decide_eq_true rfl)
def t171 : Term := .mul t106 t158
private theorem c171 : Value 1319 rel t171 [] :=
  .mul [] c106 c158 (of_decide_eq_true rfl)
def t172 : Term := .mul t166 t100
private theorem c172 : Value 1319 rel t172 [1062,1215,1121,1296,238,792,806,813,410] :=
  .mul [553,1026,947,802,124,789,928,987] c166 c100 (of_decide_eq_true rfl)
def t173 : Term := .mul t166 t102
private theorem c173 : Value 1319 rel t173 [961,818,1158,1100,524,1185,643,483,369] :=
  .mul [1045,751,289,657,531,1278,1109,306] c166 c102 (of_decide_eq_true rfl)
def t174 : Term := .mul t166 t106
private theorem c174 : Value 1319 rel t174 [375,467,219,267,1126,615,821,358,269] :=
  .mul [1305,290,979,495,497,590,66,72] c166 c106 (of_decide_eq_true rfl)
def t175 : Term := .neg t172
private theorem c175 : Value 1319 rel t175 [257,104,198,23,1081,527,513,506,909] :=
  .neg c172 (of_decide_eq_true rfl)
def t176 : Term := .neg t173
private theorem c176 : Value 1319 rel t176 [358,501,161,219,795,134,676,836,950] :=
  .neg c173 (of_decide_eq_true rfl)
def t177 : Term := .neg t174
private theorem c177 : Value 1319 rel t177 [944,852,1100,1052,193,704,498,961,1050] :=
  .neg c174 (of_decide_eq_true rfl)
def t178 : Term := .add t168 t176
private theorem c178 : Value 1319 rel t178 [857,752,927,658,381,1014,1180,1175,126] :=
  .add c168 c176 (of_decide_eq_true rfl)
def t179 : Term := .add t169 t177
private theorem c179 : Value 1319 rel t179 [] :=
  .add c169 c177 (of_decide_eq_true rfl)
def t180 : Term := .mul t106 t175
private theorem c180 : Value 1319 rel t180 [1175,381,1002,846,741,580,224,729,525] :=
  .mul [119,113,503,395,308,374,704,1023] c106 c175 (of_decide_eq_true rfl)
def t181 : Term := .mul t106 t178
private theorem c181 : Value 1319 rel t181 [143,98,183,680,333,405,1233,437,153] :=
  .mul [378,625,191,609,687,626,747,625] c106 c178 (of_decide_eq_true rfl)
def t182 : Term := .mul t106 t179
private theorem c182 : Value 1319 rel t182 [] :=
  .mul [] c106 c179 (of_decide_eq_true rfl)
def t183 : Term := .mul t106 t170
private theorem c183 : Value 1319 rel t183 [] :=
  .mul [] c106 c170 (of_decide_eq_true rfl)
def t184 : Term := .mul t106 t171
private theorem c184 : Value 1319 rel t184 [] :=
  .mul [] c106 c171 (of_decide_eq_true rfl)
def t185 : Term := .mul t178 t100
private theorem c185 : Value 1319 rel t185 [813,10,1160,848,635,443,1031,95,551] :=
  .mul [352,193,585,63,82,714,151,269] c178 c100 (of_decide_eq_true rfl)
def t186 : Term := .mul t178 t102
private theorem c186 : Value 1319 rel t186 [926,288,520,1100,1159,304,519,134,117] :=
  .mul [1115,931,247,1103,945,834,813,348] c178 c102 (of_decide_eq_true rfl)
def t187 : Term := .mul t178 t106
private theorem c187 : Value 1319 rel t187 [143,98,183,680,333,405,1233,437,153] :=
  .mul [378,625,191,609,687,626,747,625] c178 c106 (of_decide_eq_true rfl)
def t188 : Term := .neg t185
private theorem c188 : Value 1319 rel t188 [506,1309,159,471,684,876,288,1224,768] :=
  .neg c185 (of_decide_eq_true rfl)
def t189 : Term := .neg t186
private theorem c189 : Value 1319 rel t189 [393,1031,799,219,160,1015,800,1185,1202] :=
  .neg c186 (of_decide_eq_true rfl)
def t190 : Term := .neg t187
private theorem c190 : Value 1319 rel t190 [1176,1221,1136,639,986,914,86,882,1166] :=
  .neg c187 (of_decide_eq_true rfl)
def t191 : Term := .add t180 t189
private theorem c191 : Value 1319 rel t191 [249,93,482,1065,901,276,1024,595,408] :=
  .add c180 c189 (of_decide_eq_true rfl)
def t192 : Term := .add t181 t190
private theorem c192 : Value 1319 rel t192 [] :=
  .add c181 c190 (of_decide_eq_true rfl)
def t193 : Term := .mul t106 t134
private theorem c193 : Value 1319 rel t193 [854,400,233,210,924,1148,696,181,1176] :=
  .mul [144,831,901,985,245,1153,152,203] c106 c134 (of_decide_eq_true rfl)
def t194 : Term := .mul t106 t140
private theorem c194 : Value 1319 rel t194 [52,802,647,1248,1134,1191,1273,775,62] :=
  .mul [1315,934,401,613,905,501,193,295] c106 c140 (of_decide_eq_true rfl)
def t195 : Term := .mul t106 t141
private theorem c195 : Value 1319 rel t195 [45,519,520,1133,77,1266,1246,324,167] :=
  .mul [246,1101,1173,284,114,163,818,1270] c106 c141 (of_decide_eq_true rfl)
def t196 : Term := .mul t106 t139
private theorem c196 : Value 1319 rel t196 [398,778,549,1189,1225,1157,936,484,505] :=
  .mul [1076,872,1024,482,413,191,1096,1247] c106 c139 (of_decide_eq_true rfl)
def t197 : Term := .mul t139 t100
private theorem c197 : Value 1319 rel t197 [962,285,391,1277,288,1127,588,1204,821] :=
  .mul [741,1257,1010,424,403,977,602,332] c139 c100 (of_decide_eq_true rfl)
def t198 : Term := .mul t139 t102
private theorem c198 : Value 1319 rel t198 [508,200,485,1247,966,263,1100,942,528] :=
  .mul [986,140,1066,175,1308,885,532,1013] c139 c102 (of_decide_eq_true rfl)
def t199 : Term := .mul t139 t106
private theorem c199 : Value 1319 rel t199 [398,778,549,1189,1225,1157,936,484,505] :=
  .mul [1076,872,1024,482,413,191,1096,1247] c139 c106 (of_decide_eq_true rfl)
def t200 : Term := .neg t197
private theorem c200 : Value 1319 rel t200 [357,1034,928,42,1031,192,731,115,498] :=
  .neg c197 (of_decide_eq_true rfl)
def t201 : Term := .neg t198
private theorem c201 : Value 1319 rel t201 [811,1119,834,72,353,1056,219,377,791] :=
  .neg c198 (of_decide_eq_true rfl)
def t202 : Term := .neg t199
private theorem c202 : Value 1319 rel t202 [921,541,770,130,94,162,383,835,814] :=
  .neg c199 (of_decide_eq_true rfl)
def t203 : Term := .add t194 t200
private theorem c203 : Value 1319 rel t203 [409,517,256,1290,846,64,685,890,560] :=
  .add c194 c200 (of_decide_eq_true rfl)
def t204 : Term := .add t195 t201
private theorem c204 : Value 1319 rel t204 [856,319,35,1205,430,1003,146,701,958] :=
  .add c195 c201 (of_decide_eq_true rfl)
def t205 : Term := .add t196 t202
private theorem c205 : Value 1319 rel t205 [] :=
  .add c196 c202 (of_decide_eq_true rfl)
def t206 : Term := .mul t106 t193
private theorem c206 : Value 1319 rel t206 [190,306,1053,904,487,132,865,532,1004] :=
  .mul [1271,29,1043,894,260,418,352,997] c106 c193 (of_decide_eq_true rfl)
def t207 : Term := .mul t106 t203
private theorem c207 : Value 1319 rel t207 [906,134,1142,1193,154,635,429,435,675] :=
  .mul [1111,1138,907,1105,997,201,1111,726] c106 c203 (of_decide_eq_true rfl)
def t208 : Term := .mul t106 t204
private theorem c208 : Value 1319 rel t208 [843,814,842,1281,295,1289,1176,652,600] :=
  .mul [354,302,208,390,1226,1217,439,460] c106 c204 (of_decide_eq_true rfl)
def t209 : Term := .mul t106 t205
private theorem c209 : Value 1319 rel t209 [] :=
  .mul [] c106 c205 (of_decide_eq_true rfl)
def t210 : Term := .mul t204 t100
private theorem c210 : Value 1319 rel t210 [163,759,183,40,646,990,453,787,255] :=
  .mul [538,1012,1012,1146,854,986,231,810] c204 c100 (of_decide_eq_true rfl)
def t211 : Term := .mul t204 t102
private theorem c211 : Value 1319 rel t211 [301,1306,182,624,1317,532,412,1017,1222] :=
  .mul [342,116,1277,512,1192,753,51,636] c204 c102 (of_decide_eq_true rfl)
def t212 : Term := .mul t204 t106
private theorem c212 : Value 1319 rel t212 [843,814,842,1281,295,1289,1176,652,600] :=
  .mul [354,302,208,390,1226,1217,439,460] c204 c106 (of_decide_eq_true rfl)
def t213 : Term := .neg t210
private theorem c213 : Value 1319 rel t213 [1156,560,1136,1279,673,329,866,532,1064] :=
  .neg c210 (of_decide_eq_true rfl)
def t214 : Term := .neg t211
private theorem c214 : Value 1319 rel t214 [1018,13,1137,695,2,787,907,302,97] :=
  .neg c211 (of_decide_eq_true rfl)
def t215 : Term := .neg t212
private theorem c215 : Value 1319 rel t215 [476,505,477,38,1024,30,143,667,719] :=
  .neg c212 (of_decide_eq_true rfl)
def t216 : Term := .add t206 t213
private theorem c216 : Value 1319 rel t216 [27,866,870,864,1160,461,412,1064,749] :=
  .add c206 c213 (of_decide_eq_true rfl)
def t217 : Term := .add t207 t214
private theorem c217 : Value 1319 rel t217 [605,147,960,569,156,103,17,737,772] :=
  .add c207 c214 (of_decide_eq_true rfl)
def t218 : Term := .add t208 t215
private theorem c218 : Value 1319 rel t218 [] :=
  .add c208 c215 (of_decide_eq_true rfl)
def t219 : Term := .mul t106 t216
private theorem c219 : Value 1319 rel t219 [902,1091,1164,41,528,1208,507,746,524] :=
  .mul [56,1092,1244,855,167,343,52,1004] c106 c216 (of_decide_eq_true rfl)
def t220 : Term := .mul t106 t217
private theorem c220 : Value 1319 rel t220 [936,67,986,136,646,227,560,122,1184] :=
  .mul [831,1266,973,554,1273,1203,1242,982] c106 c217 (of_decide_eq_true rfl)
def t221 : Term := .mul t106 t218
private theorem c221 : Value 1319 rel t221 [] :=
  .mul [] c106 c218 (of_decide_eq_true rfl)
def t222 : Term := .mul t106 t209
private theorem c222 : Value 1319 rel t222 [] :=
  .mul [] c106 c209 (of_decide_eq_true rfl)
def t223 : Term := .mul t217 t100
private theorem c223 : Value 1319 rel t223 [756,544,579,453,1151,50,747,1192,410] :=
  .mul [1142,364,9,736,646,1202,663,1041] c217 c100 (of_decide_eq_true rfl)
def t224 : Term := .mul t217 t102
private theorem c224 : Value 1319 rel t224 [1167,976,1239,619,540,1117,352,599,1044] :=
  .mul [1059,1214,832,732,1237,1069,732,876] c217 c102 (of_decide_eq_true rfl)
def t225 : Term := .mul t217 t106
private theorem c225 : Value 1319 rel t225 [936,67,986,136,646,227,560,122,1184] :=
  .mul [831,1266,973,554,1273,1203,1242,982] c217 c106 (of_decide_eq_true rfl)
def t226 : Term := .neg t223
private theorem c226 : Value 1319 rel t226 [563,775,740,866,168,1269,572,127,909] :=
  .neg c223 (of_decide_eq_true rfl)
def t227 : Term := .neg t224
private theorem c227 : Value 1319 rel t227 [152,343,80,700,779,202,967,720,275] :=
  .neg c224 (of_decide_eq_true rfl)
def t228 : Term := .neg t225
private theorem c228 : Value 1319 rel t228 [383,1252,333,1183,673,1092,759,1197,135] :=
  .neg c225 (of_decide_eq_true rfl)
def t229 : Term := .add t219 t227
private theorem c229 : Value 1319 rel t229 [1054,115,1244,741,1307,91,155,147,799] :=
  .add c219 c227 (of_decide_eq_true rfl)
def t230 : Term := .add t220 t228
private theorem c230 : Value 1319 rel t230 [] :=
  .add c220 c228 (of_decide_eq_true rfl)
def t231 : Term := .mul t106 t226
private theorem c231 : Value 1319 rel t231 [417,195,500,1140,1217,416,84,1250,883] :=
  .mul [862,312,1106,233,1001,955,321,1023] c106 c226 (of_decide_eq_true rfl)
def t232 : Term := .mul t106 t229
private theorem c232 : Value 1319 rel t232 [220,229,1150,135,796,68,514,104,272] :=
  .mul [644,1049,1306,1160,915,1173,622,268] c106 c229 (of_decide_eq_true rfl)
def t233 : Term := .mul t106 t230
private theorem c233 : Value 1319 rel t233 [] :=
  .mul [] c106 c230 (of_decide_eq_true rfl)
def t234 : Term := .mul t106 t221
private theorem c234 : Value 1319 rel t234 [] :=
  .mul [] c106 c221 (of_decide_eq_true rfl)
def t235 : Term := .mul t106 t222
private theorem c235 : Value 1319 rel t235 [] :=
  .mul [] c106 c222 (of_decide_eq_true rfl)
def t236 : Term := .mul t229 t100
private theorem c236 : Value 1319 rel t236 [334,1318,179,641,906,452,138,1234,1079] :=
  .mul [1186,87,651,277,923,118,864,816] c229 c100 (of_decide_eq_true rfl)
def t237 : Term := .mul t229 t102
private theorem c237 : Value 1319 rel t237 [830,721,163,908,1258,556,35,434,555] :=
  .mul [132,272,943,1018,989,712,488,1139] c229 c102 (of_decide_eq_true rfl)
def t238 : Term := .mul t229 t106
private theorem c238 : Value 1319 rel t238 [220,229,1150,135,796,68,514,104,272] :=
  .mul [644,1049,1306,1160,915,1173,622,268] c229 c106 (of_decide_eq_true rfl)
def t239 : Term := .neg t236
private theorem c239 : Value 1319 rel t239 [985,1,1140,678,413,867,1181,85,240] :=
  .neg c236 (of_decide_eq_true rfl)
def t240 : Term := .neg t237
private theorem c240 : Value 1319 rel t240 [489,598,1156,411,61,763,1284,885,764] :=
  .neg c237 (of_decide_eq_true rfl)
def t241 : Term := .neg t238
private theorem c241 : Value 1319 rel t241 [1099,1090,169,1184,523,1251,805,1215,1047] :=
  .neg c238 (of_decide_eq_true rfl)
def t242 : Term := .add t231 t240
private theorem c242 : Value 1319 rel t242 [906,793,337,232,1278,1179,49,816,328] :=
  .add c231 c240 (of_decide_eq_true rfl)
def t243 : Term := .add t232 t241
private theorem c243 : Value 1319 rel t243 [] :=
  .add c232 c241 (of_decide_eq_true rfl)
def t244 : Term := .mul t106 t13
private theorem c244 : Value 1319 rel t244 [1075,456,870,385,747,151,431,1164,613] :=
  .mul [295] c106 c13 (of_decide_eq_true rfl)
def t245 : Term := .mul t106 t19
private theorem c245 : Value 1319 rel t245 [319,667,344,846,495,1043,613,608,1130] :=
  .mul [1302] c106 c19 (of_decide_eq_true rfl)
def t246 : Term := .mul t106 t25
private theorem c246 : Value 1319 rel t246 [101,1240,622,331,774,866,30,935,638] :=
  .mul [919] c106 c25 (of_decide_eq_true rfl)
def t247 : Term := .mul t106 t27
private theorem c247 : Value 1319 rel t247 [880,1055,693,885,902,1177,137,385,60] :=
  .mul [1146] c106 c27 (of_decide_eq_true rfl)
def t248 : Term := .neg t100
private theorem c248 : Value 1319 rel t248 [1267,78,1278,1200,381,203,1153,529,448] :=
  .neg c100 (of_decide_eq_true rfl)
def t249 : Term := .neg t102
private theorem c249 : Value 1319 rel t249 [322,507,596,379,609,91,489,1112,1065] :=
  .neg c102 (of_decide_eq_true rfl)
def t250 : Term := .neg t106
private theorem c250 : Value 1319 rel t250 [325,1034,865,1127,221,128,537,248,173] :=
  .neg c106 (of_decide_eq_true rfl)
def t251 : Term := .add t246 t248
private theorem c251 : Value 1319 rel t251 [49,1318,581,212,1155,1069,1183,145,1086] :=
  .add c246 c248 (of_decide_eq_true rfl)
def t252 : Term := .add t247 t249
private theorem c252 : Value 1319 rel t252 [1202,243,1289,1264,192,1268,626,178,1125] :=
  .add c247 c249 (of_decide_eq_true rfl)
def t253 : Term := .add t106 t250
private theorem c253 : Value 1319 rel t253 [] :=
  .add c106 c250 (of_decide_eq_true rfl)
def t254 : Term := .mul t106 t244
private theorem c254 : Value 1319 rel t254 [515,135,77,822,905,668,1010,1009,1044] :=
  .mul [1138,1182,807,115,13,63,544,790] c106 c244 (of_decide_eq_true rfl)
def t255 : Term := .mul t106 t245
private theorem c255 : Value 1319 rel t255 [1316,1252,1234,628,858,991,140,200,647] :=
  .mul [266,853,1154,284,0,971,311,1041] c106 c245 (of_decide_eq_true rfl)
def t256 : Term := .mul t106 t251
private theorem c256 : Value 1319 rel t256 [474,587,500,935,1216,1129,993,1079,315] :=
  .mul [987,901,790,787,104,120,664,739] c106 c251 (of_decide_eq_true rfl)
def t257 : Term := .mul t106 t252
private theorem c257 : Value 1319 rel t257 [409,487,258,763,783,392,1182,401,615] :=
  .mul [698,409,1201,502,553,1002,948,587] c106 c252 (of_decide_eq_true rfl)
def t258 : Term := .mul t106 t253
private theorem c258 : Value 1319 rel t258 [] :=
  .mul [] c106 c253 (of_decide_eq_true rfl)
def t259 : Term := .mul t252 t100
private theorem c259 : Value 1319 rel t259 [1006,1249,221,420,404,1278,182,1188,293] :=
  .mul [918,128,356,161,347,911,1053,1177] c252 c100 (of_decide_eq_true rfl)
def t260 : Term := .mul t252 t102
private theorem c260 : Value 1319 rel t260 [1011,1029,910,456,1079,500,998,1177,498] :=
  .mul [331,202,360,746,517,1085,772,846] c252 c102 (of_decide_eq_true rfl)
def t261 : Term := .mul t252 t106
private theorem c261 : Value 1319 rel t261 [409,487,258,763,783,392,1182,401,615] :=
  .mul [698,409,1201,502,553,1002,948,587] c252 c106 (of_decide_eq_true rfl)
def t262 : Term := .neg t259
private theorem c262 : Value 1319 rel t262 [313,70,1098,899,915,41,1137,131,1026] :=
  .neg c259 (of_decide_eq_true rfl)
def t263 : Term := .neg t260
private theorem c263 : Value 1319 rel t263 [308,290,409,863,240,819,321,142,821] :=
  .neg c260 (of_decide_eq_true rfl)
def t264 : Term := .neg t261
private theorem c264 : Value 1319 rel t264 [910,832,1061,556,536,927,137,918,704] :=
  .neg c261 (of_decide_eq_true rfl)
def t265 : Term := .add t255 t262
private theorem c265 : Value 1319 rel t265 [310,3,1013,208,454,1032,1277,331,354] :=
  .add c255 c262 (of_decide_eq_true rfl)
def t266 : Term := .add t256 t263
private theorem c266 : Value 1319 rel t266 [782,877,909,479,137,629,1314,1221,1136] :=
  .add c256 c263 (of_decide_eq_true rfl)
def t267 : Term := .add t257 t264
private theorem c267 : Value 1319 rel t267 [] :=
  .add c257 c264 (of_decide_eq_true rfl)
def t268 : Term := .mul t106 t254
private theorem c268 : Value 1319 rel t268 [139,657,437,1306,544,472,1019,166,1191] :=
  .mul [1129,746,625,491,373,1011,380,91] c106 c254 (of_decide_eq_true rfl)
def t269 : Term := .mul t106 t265
private theorem c269 : Value 1319 rel t269 [17,899,1211,202,253,1120,1283,566,213] :=
  .mul [874,161,141,1140,1197,732,1092,751] c106 c265 (of_decide_eq_true rfl)
def t270 : Term := .mul t106 t266
private theorem c270 : Value 1319 rel t270 [839,930,139,775,1043,793,824,474,891] :=
  .mul [279,277,328,313,95,905,704,3] c106 c266 (of_decide_eq_true rfl)
def t271 : Term := .mul t106 t267
private theorem c271 : Value 1319 rel t271 [] :=
  .mul [] c106 c267 (of_decide_eq_true rfl)
def t272 : Term := .mul t106 t258
private theorem c272 : Value 1319 rel t272 [] :=
  .mul [] c106 c258 (of_decide_eq_true rfl)
def t273 : Term := .mul t266 t100
private theorem c273 : Value 1319 rel t273 [857,161,730,169,249,63,204,1145,157] :=
  .mul [184,568,182,203,1059,802,927,206] c266 c100 (of_decide_eq_true rfl)
def t274 : Term := .mul t266 t102
private theorem c274 : Value 1319 rel t274 [866,718,421,216,570,1019,348,116,1036] :=
  .mul [343,748,342,562,1286,1168,416,1002] c266 c102 (of_decide_eq_true rfl)
def t275 : Term := .mul t266 t106
private theorem c275 : Value 1319 rel t275 [839,930,139,775,1043,793,824,474,891] :=
  .mul [279,277,328,313,95,905,704,3] c266 c106 (of_decide_eq_true rfl)
def t276 : Term := .neg t273
private theorem c276 : Value 1319 rel t276 [462,1158,589,1150,1070,1256,1115,174,1162] :=
  .neg c273 (of_decide_eq_true rfl)
def t277 : Term := .neg t274
private theorem c277 : Value 1319 rel t277 [453,601,898,1103,749,300,971,1203,283] :=
  .neg c274 (of_decide_eq_true rfl)
def t278 : Term := .neg t275
private theorem c278 : Value 1319 rel t278 [480,389,1180,544,276,526,495,845,428] :=
  .neg c275 (of_decide_eq_true rfl)
def t279 : Term := .add t268 t276
private theorem c279 : Value 1319 rel t279 [601,496,1026,1137,295,409,815,340,1034] :=
  .add c268 c276 (of_decide_eq_true rfl)
def t280 : Term := .add t269 t277
private theorem c280 : Value 1319 rel t280 [470,181,790,1305,1002,101,935,450,496] :=
  .add c269 c277 (of_decide_eq_true rfl)
def t281 : Term := .add t270 t278
private theorem c281 : Value 1319 rel t281 [] :=
  .add c270 c278 (of_decide_eq_true rfl)
def t282 : Term := .mul t106 t279
private theorem c282 : Value 1319 rel t282 [366,749,1092,546,176,241,1006,100,905] :=
  .mul [1,350,1212,816,879,508,267,502] c106 c279 (of_decide_eq_true rfl)
def t283 : Term := .mul t106 t280
private theorem c283 : Value 1319 rel t283 [169,489,860,12,826,0,202,918,186] :=
  .mul [322,179,469,1094,941,602,567,1246] c106 c280 (of_decide_eq_true rfl)
def t284 : Term := .mul t106 t281
private theorem c284 : Value 1319 rel t284 [] :=
  .mul [] c106 c281 (of_decide_eq_true rfl)
def t285 : Term := .mul t106 t271
private theorem c285 : Value 1319 rel t285 [] :=
  .mul [] c106 c271 (of_decide_eq_true rfl)
def t286 : Term := .mul t106 t272
private theorem c286 : Value 1319 rel t286 [] :=
  .mul [] c106 c272 (of_decide_eq_true rfl)
def t287 : Term := .mul t280 t100
private theorem c287 : Value 1319 rel t287 [765,981,351,493,1192,307,596,671,1235] :=
  .mul [460,920,239,811,648,945,893,703] c280 c100 (of_decide_eq_true rfl)
def t288 : Term := .mul t280 t102
private theorem c288 : Value 1319 rel t288 [491,734,1041,1187,108,910,393,486,943] :=
  .mul [1278,1250,1131,950,1,446,1011,679] c280 c102 (of_decide_eq_true rfl)
def t289 : Term := .mul t280 t106
private theorem c289 : Value 1319 rel t289 [169,489,860,12,826,0,202,918,186] :=
  .mul [322,179,469,1094,941,602,567,1246] c280 c106 (of_decide_eq_true rfl)
def t290 : Term := .neg t287
private theorem c290 : Value 1319 rel t290 [554,338,968,826,127,1012,723,648,84] :=
  .neg c287 (of_decide_eq_true rfl)
def t291 : Term := .neg t288
private theorem c291 : Value 1319 rel t291 [828,585,278,132,1211,409,926,833,376] :=
  .neg c288 (of_decide_eq_true rfl)
def t292 : Term := .neg t289
private theorem c292 : Value 1319 rel t292 [1150,830,459,1307,493,0,1117,401,1133] :=
  .neg c289 (of_decide_eq_true rfl)
def t293 : Term := .add t282 t291
private theorem c293 : Value 1319 rel t293 [1194,15,51,678,68,650,613,933,1281] :=
  .add c282 c291 (of_decide_eq_true rfl)
def t294 : Term := .add t283 t292
private theorem c294 : Value 1319 rel t294 [] :=
  .add c283 c292 (of_decide_eq_true rfl)
def t295 : Term := .mul t63 t2
private theorem c295 : Value 1319 rel t295 [343,1139,458,225,756,239,742,1280,104] :=
  .mul [523,376,759,432,622,868,809,785] c63 c2 (of_decide_eq_true rfl)
def t296 : Term := .mul t295 t2
private theorem c296 : Value 1319 rel t296 [1081,178,369,842,227,804,196,655,929] :=
  .mul [1177,255,567,44,444,1009,881,824] c295 c2 (of_decide_eq_true rfl)
def t297 : Term := .raw [378]
private theorem c297 : Value 1319 rel t297 [378] := .raw [378]
def t298 : Term := .mul t297 t296
private theorem c298 : Value 1319 rel t298 [1047,15,987,397,71,542,224,937,308] :=
  .mul [] c297 c296 (of_decide_eq_true rfl)
def t299 : Term := .raw [882]
private theorem c299 : Value 1319 rel t299 [882] := .raw [882]
def t300 : Term := .mul t299 t295
private theorem c300 : Value 1319 rel t300 [475,839,342,600,697,1077,220,1215,717] :=
  .mul [] c299 c295 (of_decide_eq_true rfl)
def t301 : Term := .neg t300
private theorem c301 : Value 1319 rel t301 [844,480,977,719,622,242,1099,104,602] :=
  .neg c300 (of_decide_eq_true rfl)
def t302 : Term := .add t298 t301
private theorem c302 : Value 1319 rel t302 [572,495,645,1116,693,784,4,1041,910] :=
  .add c298 c301 (of_decide_eq_true rfl)
def t303 : Term := .raw [753]
private theorem c303 : Value 1319 rel t303 [753] := .raw [753]
def t304 : Term := .mul t303 t63
private theorem c304 : Value 1319 rel t304 [857,416,1214,348,715,601,893,700,114] :=
  .mul [] c303 c63 (of_decide_eq_true rfl)
def t305 : Term := .add t302 t304
private theorem c305 : Value 1319 rel t305 [110,911,540,145,89,66,897,422,1024] :=
  .add c302 c304 (of_decide_eq_true rfl)
def t306 : Term := .raw [280]
private theorem c306 : Value 1319 rel t306 [280] := .raw [280]
def t307 : Term := .mul t306 t2
private theorem c307 : Value 1319 rel t307 [794,13,235,510,258,1309,1273,953,798] :=
  .mul [] c306 c2 (of_decide_eq_true rfl)
def t308 : Term := .neg t307
private theorem c308 : Value 1319 rel t308 [525,1306,1084,809,1061,10,46,366,521] :=
  .neg c307 (of_decide_eq_true rfl)
def t309 : Term := .add t305 t308
private theorem c309 : Value 1319 rel t309 [635,898,305,954,1150,76,943,788,226] :=
  .add c305 c308 (of_decide_eq_true rfl)
def t310 : Term := .raw [40]
private theorem c310 : Value 1319 rel t310 [40] := .raw [40]
def t311 : Term := .add t309 t310
private theorem c311 : Value 1319 rel t311 [675,898,305,954,1150,76,943,788,226] :=
  .add c309 c310 (of_decide_eq_true rfl)
def t312 : Term := .mul t85 t85
private theorem c312 : Value 1319 rel t312 [815,1281,34,270,1209,830,1243,40,594] :=
  .mul [1067,901,908,364,1133,631,285,1280] c85 c85 (of_decide_eq_true rfl)
def t313 : Term := .mul t311 t312
private theorem c313 : Value 1319 rel t313 [204,565,1178,912,922,825,1094,806,1125] :=
  .mul [405,57,193,903,553,1261,65,1025] c311 c312 (of_decide_eq_true rfl)
def t314 : Term := .mul t296 t2
private theorem c314 : Value 1319 rel t314 [1235,214,386,977,686,1005,540,408,1025] :=
  .mul [1163,900,727,1210,584,252,372,867] c296 c2 (of_decide_eq_true rfl)
def t315 : Term := .raw [949]
private theorem c315 : Value 1319 rel t315 [949] := .raw [949]
def t316 : Term := .mul t315 t314
private theorem c316 : Value 1319 rel t316 [743,1279,951,1235,747,108,688,725,622] :=
  .mul [] c315 c314 (of_decide_eq_true rfl)
def t317 : Term := .raw [1205]
private theorem c317 : Value 1319 rel t317 [1205] := .raw [1205]
def t318 : Term := .mul t317 t296
private theorem c318 : Value 1319 rel t318 [752,812,142,299,502,674,79,513,933] :=
  .mul [] c317 c296 (of_decide_eq_true rfl)
def t319 : Term := .neg t318
private theorem c319 : Value 1319 rel t319 [567,507,1177,1020,817,645,1240,806,386] :=
  .neg c318 (of_decide_eq_true rfl)
def t320 : Term := .add t316 t319
private theorem c320 : Value 1319 rel t320 [1310,467,809,936,245,753,609,212,1008] :=
  .add c316 c319 (of_decide_eq_true rfl)
def t321 : Term := .raw [1302]
private theorem c321 : Value 1319 rel t321 [1302] := .raw [1302]
def t322 : Term := .mul t321 t295
private theorem c322 : Value 1319 rel t322 [764,422,128,132,338,1213,576,663,870] :=
  .mul [] c321 c295 (of_decide_eq_true rfl)
def t323 : Term := .add t320 t322
private theorem c323 : Value 1319 rel t323 [755,889,937,1068,583,647,1185,875,559] :=
  .add c320 c322 (of_decide_eq_true rfl)
def t324 : Term := .raw [912]
private theorem c324 : Value 1319 rel t324 [912] := .raw [912]
def t325 : Term := .mul t324 t63
private theorem c325 : Value 1319 rel t325 [1080,672,845,968,1155,565,225,522,590] :=
  .mul [] c324 c63 (of_decide_eq_true rfl)
def t326 : Term := .add t323 t325
private theorem c326 : Value 1319 rel t326 [516,242,463,717,419,1212,91,78,1149] :=
  .add c323 c325 (of_decide_eq_true rfl)
def t327 : Term := .raw [660]
private theorem c327 : Value 1319 rel t327 [660] := .raw [660]
def t328 : Term := .mul t327 t2
private theorem c328 : Value 1319 rel t328 [741,1067,1025,260,985,1107,80,1210,562] :=
  .mul [] c327 c2 (of_decide_eq_true rfl)
def t329 : Term := .neg t328
private theorem c329 : Value 1319 rel t329 [578,252,294,1059,334,212,1239,109,757] :=
  .neg c328 (of_decide_eq_true rfl)
def t330 : Term := .add t326 t329
private theorem c330 : Value 1319 rel t330 [1094,494,757,457,753,105,11,187,587] :=
  .add c326 c329 (of_decide_eq_true rfl)
def t331 : Term := .raw [120]
private theorem c331 : Value 1319 rel t331 [120] := .raw [120]
def t332 : Term := .add t330 t331
private theorem c332 : Value 1319 rel t332 [1214,494,757,457,753,105,11,187,587] :=
  .add c330 c331 (of_decide_eq_true rfl)
def t333 : Term := .mul t332 t85
private theorem c333 : Value 1319 rel t333 [957,115,1144,1186,307,914,630,224,568] :=
  .mul [631,350,575,428,1303,1206,141,902] c332 c85 (of_decide_eq_true rfl)
def t334 : Term := .mul t333 t99
private theorem c334 : Value 1319 rel t334 [79,1060,465,434,482,803,657,810,893] :=
  .mul [727,961,1308,644,45,1265,244,1284] c333 c99 (of_decide_eq_true rfl)
def t335 : Term := .neg t334
private theorem c335 : Value 1319 rel t335 [1240,259,854,885,837,516,662,509,426] :=
  .neg c334 (of_decide_eq_true rfl)
def t336 : Term := .add t313 t335
private theorem c336 : Value 1319 rel t336 [125,824,713,478,440,22,437,1315,232] :=
  .add c313 c335 (of_decide_eq_true rfl)
def t337 : Term := .mul t314 t2
private theorem c337 : Value 1319 rel t337 [811,819,358,302,904,282,591,948,191] :=
  .mul [1140,643,1131,1039,544,1100,731,613] c314 c2 (of_decide_eq_true rfl)
def t338 : Term := .raw [8]
private theorem c338 : Value 1319 rel t338 [8] := .raw [8]
def t339 : Term := .mul t338 t337
private theorem c339 : Value 1319 rel t339 [1212,1276,226,1097,637,937,771,989,209] :=
  .mul [] c338 c337 (of_decide_eq_true rfl)
def t340 : Term := .neg t316
private theorem c340 : Value 1319 rel t340 [576,40,368,84,572,1211,631,594,697] :=
  .neg c316 (of_decide_eq_true rfl)
def t341 : Term := .add t339 t340
private theorem c341 : Value 1319 rel t341 [469,1316,594,1181,1209,829,83,264,906] :=
  .add c339 c340 (of_decide_eq_true rfl)
def t342 : Term := .mul t315 t296
private theorem c342 : Value 1319 rel t342 [1006,90,646,1063,426,614,25,346,529] :=
  .mul [] c315 c296 (of_decide_eq_true rfl)
def t343 : Term := .neg t342
private theorem c343 : Value 1319 rel t343 [313,1229,673,256,893,705,1294,973,790] :=
  .neg c342 (of_decide_eq_true rfl)
def t344 : Term := .add t341 t343
private theorem c344 : Value 1319 rel t344 [782,1226,1267,118,783,215,58,1237,377] :=
  .add c341 c343 (of_decide_eq_true rfl)
def t345 : Term := .raw [1201]
private theorem c345 : Value 1319 rel t345 [1201] := .raw [1201]
def t346 : Term := .mul t345 t295
private theorem c346 : Value 1319 rel t346 [415,136,35,1149,484,816,817,645,918] :=
  .mul [] c345 c295 (of_decide_eq_true rfl)
def t347 : Term := .add t344 t346
private theorem c347 : Value 1319 rel t347 [1197,43,1302,1267,1267,1031,875,563,1295] :=
  .add c344 c346 (of_decide_eq_true rfl)
def t348 : Term := .raw [144]
private theorem c348 : Value 1319 rel t348 [144] := .raw [144]
def t349 : Term := .mul t348 t63
private theorem c349 : Value 1319 rel t349 [1073,1078,64,14,946,714,938,13,232] :=
  .mul [] c348 c63 (of_decide_eq_true rfl)
def t350 : Term := .neg t349
private theorem c350 : Value 1319 rel t350 [246,241,1255,1305,373,605,381,1306,1087] :=
  .neg c349 (of_decide_eq_true rfl)
def t351 : Term := .add t347 t350
private theorem c351 : Value 1319 rel t351 [124,284,1238,1253,321,317,1256,550,1063] :=
  .add c347 c350 (of_decide_eq_true rfl)
def t352 : Term := .raw [360]
private theorem c352 : Value 1319 rel t352 [360] := .raw [360]
def t353 : Term := .mul t352 t2
private theorem c353 : Value 1319 rel t353 [644,582,679,1221,897,364,883,660,1026] :=
  .mul [] c352 c2 (of_decide_eq_true rfl)
def t354 : Term := .neg t353
private theorem c354 : Value 1319 rel t354 [675,737,640,98,422,955,436,659,293] :=
  .neg c353 (of_decide_eq_true rfl)
def t355 : Term := .add t351 t354
private theorem c355 : Value 1319 rel t355 [799,1021,559,32,743,1272,373,1209,37] :=
  .add c351 c354 (of_decide_eq_true rfl)
def t356 : Term := .raw [90]
private theorem c356 : Value 1319 rel t356 [90] := .raw [90]
def t357 : Term := .add t355 t356
private theorem c357 : Value 1319 rel t357 [889,1021,559,32,743,1272,373,1209,37] :=
  .add c355 c356 (of_decide_eq_true rfl)
def t358 : Term := .mul t99 t99
private theorem c358 : Value 1319 rel t358 [157,253,224,271,8,926,95,858,191] :=
  .mul [529,665,625,1205,522,719,838,338] c99 c99 (of_decide_eq_true rfl)
def t359 : Term := .mul t357 t358
private theorem c359 : Value 1319 rel t359 [60,700,267,928,948,466,553,299,1221] :=
  .mul [846,81,689,415,106,1310,829,472] c357 c358 (of_decide_eq_true rfl)
def t360 : Term := .add t336 t359
private theorem c360 : Value 1319 rel t360 [185,205,980,87,69,488,990,295,134] :=
  .add c336 c359 (of_decide_eq_true rfl)
def t361 : Term := .mul t188 t293
private theorem c361 : Value 1319 rel t361 [897,297,729,1068,1046,502,569,976,60] :=
  .mul [949,152,419,1182,816,470,340,1153] c188 c293 (of_decide_eq_true rfl)
def t362 : Term := .mul t191 t290
private theorem c362 : Value 1319 rel t362 [931,861,596,543,759,180,183,767,355] :=
  .mul [1066,897,517,1143,1129,531,887,1297] c191 c290 (of_decide_eq_true rfl)
def t363 : Term := .neg t362
private theorem c363 : Value 1319 rel t363 [388,458,723,776,560,1139,1136,552,964] :=
  .neg c362 (of_decide_eq_true rfl)
def t364 : Term := .add t361 t363
private theorem c364 : Value 1319 rel t364 [1285,755,133,525,287,322,386,209,1024] :=
  .add c361 c363 (of_decide_eq_true rfl)
def t365 : Term := .mul t106 t364
private theorem c365 : Value 1319 rel t365 [590,810,1102,248,127,618,913,988,489] :=
  .mul [986,1243,186,694,748,53,729,913] c106 c364 (of_decide_eq_true rfl)
def t366 : Term := .mul t239 t293
private theorem c366 : Value 1319 rel t366 [1318,482,633,1252,1054,71,1142,1174,1103] :=
  .mul [224,1096,864,366,627,1231,1189,113] c239 c293 (of_decide_eq_true rfl)
def t367 : Term := .mul t242 t290
private theorem c367 : Value 1319 rel t367 [664,616,1016,503,842,997,663,593,835] :=
  .mul [1005,182,619,263,1127,523,1016,1172] c242 c290 (of_decide_eq_true rfl)
def t368 : Term := .neg t367
private theorem c368 : Value 1319 rel t368 [655,703,303,816,477,322,656,726,484] :=
  .neg c367 (of_decide_eq_true rfl)
def t369 : Term := .add t366 t368
private theorem c369 : Value 1319 rel t369 [654,1185,936,749,212,393,479,581,268] :=
  .add c366 c368 (of_decide_eq_true rfl)
def t370 : Term := .mul t365 t369
private theorem c370 : Value 1319 rel t370 [469,1154,34,998,243,352,476,1268,158] :=
  .mul [5,920,322,1039,36,16,1154,471] c365 c369 (of_decide_eq_true rfl)
def t371 : Term := .mul t370 t360
private theorem c371 : Value 1319 rel t371 [1204,200,1198,1014,802,640,822,1113,1236] :=
  .mul [1234,322,1175,1001,517,36,869,68] c370 c360 (of_decide_eq_true rfl)
def t372 : Term := .raw [410,657,1099,69,422,438,345,936,690]
private theorem c372 : Value 1319 rel t372 [410,657,1099,69,422,438,345,936,690] := .raw [410,657,1099,69,422,438,345,936,690]
def t373 : Term := .mul t371 t372
private theorem c373 : Value 1319 rel t373 [1] :=
  .mul [1277,530,36,618,105,64,659,766] c371 c372 (of_decide_eq_true rfl)
def t374 : Term := .raw [996,390,644,587,149,349,1167,1078,1245,289,254,928,682,891]
private theorem c374 : Value 1319 rel t374 [996,390,644,587,149,349,1167,1078,1245,289,254,928,682,891] := .raw [996,390,644,587,149,349,1167,1078,1245,289,254,928,682,891]
def t375 : Term := .raw [1302,424,383,339,468,476,1123,357,159,379,1112,220,137,1154,891]
private theorem c375 : Value 1319 rel t375 [1302,424,383,339,468,476,1123,357,159,379,1112,220,137,1154,891] := .raw [1302,424,383,339,468,476,1123,357,159,379,1112,220,137,1154,891]
def t376 : Term := .mul t3 t374
private theorem c376 : Value 1319 rel t376 [937,153,1056,1280,1030,72,578,817,612] :=
  .mul [343,916,283,1074,630,46,535,945,815,981,711,886,80] c3 c374 (of_decide_eq_true rfl)
def t377 : Term := .add t375 t376
private theorem c377 : Value 1319 rel t377 [920,577,120,300,179,548,382,1174,771,379,1112,220,137,1154,891] :=
  .add c375 c376 (of_decide_eq_true rfl)
def t378 : Term := .raw [1188,925,178,1021,579,618,355,767,584,715,1239,440,564,353,258]
private theorem c378 : Value 1319 rel t378 [1188,925,178,1021,579,618,355,767,584,715,1239,440,564,353,258] := .raw [1188,925,178,1021,579,618,355,767,584,715,1239,440,564,353,258]
def t379 : Term := .mul t3 t377
private theorem c379 : Value 1319 rel t379 [702,1153,276,676,1301,1197,349,335,1215] :=
  .mul [685,564,701,1239,892,615,22,1114,591,586,1050,1105,354,80] c3 c377 (of_decide_eq_true rfl)
def t380 : Term := .add t378 t379
private theorem c380 : Value 1319 rel t380 [571,759,454,378,561,496,704,1102,480,715,1239,440,564,353,258] :=
  .add c378 c379 (of_decide_eq_true rfl)
def t381 : Term := .raw [1268,338,1200,242,133,1203,988,1229,748,74,539,433,8,59,90]
private theorem c381 : Value 1319 rel t381 [1268,338,1200,242,133,1203,988,1229,748,74,539,433,8,59,90] := .raw [1268,338,1200,242,133,1203,988,1229,748,74,539,433,8,59,90]
def t382 : Term := .mul t3 t380
private theorem c382 : Value 1319 rel t382 [663,498,814,866,824,269,929,770,571] :=
  .mul [1159,1231,1079,824,488,531,440,945,273,146,374,564,502,827] c3 c380 (of_decide_eq_true rfl)
def t383 : Term := .add t381 t382
private theorem c383 : Value 1319 rel t383 [612,836,695,1108,957,153,598,680,0,74,539,433,8,59,90] :=
  .add c381 c382 (of_decide_eq_true rfl)
def t384 : Term := .raw [391,444,114,2,738,1220,512,321,974]
private theorem c384 : Value 1319 rel t384 [391,444,114,2,738,1220,512,321,974] := .raw [391,444,114,2,738,1220,512,321,974]
def t385 : Term := .mul t383 t384
private theorem c385 : Value 1319 rel t385 [1] :=
  .mul [679,1153,1160,380,1018,834,296,508,938,1052,610,147,594,606] c383 c384 (of_decide_eq_true rfl)
def t386 : Term := .mul t4 t374
private theorem c386 : Value 1319 rel t386 [197,1174,592,1134,505,752,1128,247,392] :=
  .mul [678,1027,843,801,875,1118,384,774,643,1260,575,820,576] c4 c374 (of_decide_eq_true rfl)
def t387 : Term := .add t375 t386
private theorem c387 : Value 1319 rel t387 [180,279,975,154,973,1228,932,604,551,379,1112,220,137,1154,891] :=
  .add c375 c386 (of_decide_eq_true rfl)
def t388 : Term := .mul t4 t387
private theorem c388 : Value 1319 rel t388 [728,991,1073,1144,1172,1204,52,14,1254] :=
  .mul [1198,1202,183,1307,453,318,718,949,1,620,918,916,419,576] c4 c387 (of_decide_eq_true rfl)
def t389 : Term := .add t378 t388
private theorem c389 : Value 1319 rel t389 [597,597,1251,846,432,503,407,781,519,715,1239,440,564,353,258] :=
  .add c378 c388 (of_decide_eq_true rfl)
def t390 : Term := .mul t4 t389
private theorem c390 : Value 1319 rel t390 [1192,603,840,142,1165,567,433,1074,60] :=
  .mul [1077,456,920,1000,66,95,670,1295,1170,17,177,553,977,1206] c4 c389 (of_decide_eq_true rfl)
def t391 : Term := .add t381 t390
private theorem c391 : Value 1319 rel t391 [1141,941,721,384,1298,451,102,984,808,74,539,433,8,59,90] :=
  .add c381 c390 (of_decide_eq_true rfl)
def t392 : Term := .raw [1002,887,656,370,53,1151,301,672,67]
private theorem c392 : Value 1319 rel t392 [1002,887,656,370,53,1151,301,672,67] := .raw [1002,887,656,370,53,1151,301,672,67]
def t393 : Term := .mul t391 t392
private theorem c393 : Value 1319 rel t393 [1] :=
  .mul [1237,512,946,316,411,176,349,1012,516,172,910,970,1218,754] c391 c392 (of_decide_eq_true rfl)
def t394 : Term := .raw [867,1059,1253,121]
private theorem c394 : Value 1319 rel t394 [867,1059,1253,121] := .raw [867,1059,1253,121]
def t395 : Term := .raw [433,550,17,25,121]
private theorem c395 : Value 1319 rel t395 [433,550,17,25,121] := .raw [433,550,17,25,121]
def t396 : Term := .mul t2 t394
private theorem c396 : Value 1319 rel t396 [720,600,210,863,601,546,351,1111,266] :=
  .mul [483,126,147] c2 c394 (of_decide_eq_true rfl)
def t397 : Term := .add t395 t396
private theorem c397 : Value 1319 rel t397 [1153,1150,227,888,722,546,351,1111,266] :=
  .add c395 c396 (of_decide_eq_true rfl)
def t398 : Term := .raw [1088,1228,460,773,811]
private theorem c398 : Value 1319 rel t398 [1088,1228,460,773,811] := .raw [1088,1228,460,773,811]
def t399 : Term := .mul t2 t397
private theorem c399 : Value 1319 rel t399 [1051,1290,476,1094,314,1115,61,220,403] :=
  .mul [1240,1198,1051,436,1200,722,1142,890] c2 c397 (of_decide_eq_true rfl)
def t400 : Term := .add t398 t399
private theorem c400 : Value 1319 rel t400 [820,1199,936,548,1125,1115,61,220,403] :=
  .add c398 c399 (of_decide_eq_true rfl)
def t401 : Term := .raw [674,862,828,204,926]
private theorem c401 : Value 1319 rel t401 [674,862,828,204,926] := .raw [674,862,828,204,926]
def t402 : Term := .mul t2 t400
private theorem c402 : Value 1319 rel t402 [620,466,804,312,969,85,755,430,81] :=
  .mul [284,744,244,881,418,593,292,555] c2 c400 (of_decide_eq_true rfl)
def t403 : Term := .add t401 t402
private theorem c403 : Value 1319 rel t403 [1294,9,313,516,576,85,755,430,81] :=
  .add c401 c402 (of_decide_eq_true rfl)
def t404 : Term := .raw [979,117,238,1274,121]
private theorem c404 : Value 1319 rel t404 [979,117,238,1274,121] := .raw [979,117,238,1274,121]
def t405 : Term := .raw [1118,273,990,1305,46,121]
private theorem c405 : Value 1319 rel t405 [1118,273,990,1305,46,121] := .raw [1118,273,990,1305,46,121]
def t406 : Term := .mul t2 t404
private theorem c406 : Value 1319 rel t406 [1180,499,1083,1062,1097,1119,269,1008,221] :=
  .mul [1126,991,1307,147] c2 c404 (of_decide_eq_true rfl)
def t407 : Term := .add t405 t406
private theorem c407 : Value 1319 rel t407 [979,772,754,1048,1143,1240,269,1008,221] :=
  .add c405 c406 (of_decide_eq_true rfl)
def t408 : Term := .raw [592,477,226,83,914,811]
private theorem c408 : Value 1319 rel t408 [592,477,226,83,914,811] := .raw [592,477,226,83,914,811]
def t409 : Term := .mul t2 t407
private theorem c409 : Value 1319 rel t409 [9,1287,1031,1219,269,26,970,2,163] :=
  .mul [705,322,418,1103,948,32,851,432] c2 c407 (of_decide_eq_true rfl)
def t410 : Term := .add t408 t409
private theorem c410 : Value 1319 rel t410 [601,445,1257,1302,1183,837,970,2,163] :=
  .add c408 c409 (of_decide_eq_true rfl)
def t411 : Term := .raw [840,475,648,718,768,926]
private theorem c411 : Value 1319 rel t411 [840,475,648,718,768,926] := .raw [840,475,648,718,768,926]
def t412 : Term := .mul t2 t410
private theorem c412 : Value 1319 rel t412 [736,591,725,50,662,898,768,341,768] :=
  .mul [535,954,409,655,942,126,80,1190] c2 c410 (of_decide_eq_true rfl)
def t413 : Term := .add t411 t412
private theorem c413 : Value 1319 rel t413 [257,1066,54,768,111,505,768,341,768] :=
  .add c411 c412 (of_decide_eq_true rfl)
def t414 : Term := .mul t4 t403
private theorem c414 : Value 1319 rel t414 [1128,772,733,837,581,588,1171,871,824] :=
  .mul [425,1283,561,547,809,759,459,532] c4 c403 (of_decide_eq_true rfl)
def t415 : Term := .add t413 t414
private theorem c415 : Value 1319 rel t415 [66,519,787,286,692,1093,620,1212,273] :=
  .add c413 c414 (of_decide_eq_true rfl)
def t416 : Term := .raw [386,843,221,310,741]
private theorem c416 : Value 1319 rel t416 [386,843,221,310,741] := .raw [386,843,221,310,741]
def t417 : Term := .raw [851,770,340,469,486,741]
private theorem c417 : Value 1319 rel t417 [851,770,340,469,486,741] := .raw [851,770,340,469,486,741]
def t418 : Term := .mul t2 t416
private theorem c418 : Value 1319 rel t418 [1221,637,16,1021,1215,594,836,52,1034] :=
  .mul [477,467,459,595] c2 c416 (of_decide_eq_true rfl)
def t419 : Term := .add t417 t418
private theorem c419 : Value 1319 rel t419 [753,88,356,171,382,16,836,52,1034] :=
  .add c417 c418 (of_decide_eq_true rfl)
def t420 : Term := .raw [1023,963,56,907,830,1206]
private theorem c420 : Value 1319 rel t420 [1023,963,56,907,830,1206] := .raw [1023,963,56,907,830,1206]
def t421 : Term := .mul t2 t419
private theorem c421 : Value 1319 rel t421 [510,152,119,1312,25,333,1182,552,696] :=
  .mul [1196,668,157,540,1298,316,626,177] c2 c419 (of_decide_eq_true rfl)
def t422 : Term := .add t420 t421
private theorem c422 : Value 1319 rel t422 [214,1115,175,900,855,220,1182,552,696] :=
  .add c420 c421 (of_decide_eq_true rfl)
def t423 : Term := .raw [664,1135,747,437,496,1027]
private theorem c423 : Value 1319 rel t423 [664,1135,747,437,496,1027] := .raw [664,1135,747,437,496,1027]
def t424 : Term := .mul t2 t422
private theorem c424 : Value 1319 rel t424 [1179,770,76,1226,984,117,1054,612,298] :=
  .mul [1144,952,337,1213,168,92,162,137] c2 c422 (of_decide_eq_true rfl)
def t425 : Term := .add t423 t424
private theorem c425 : Value 1319 rel t425 [524,586,823,344,161,1144,1054,612,298] :=
  .add c423 c424 (of_decide_eq_true rfl)
def t426 : Term := .mul t4 t415
private theorem c426 : Value 1319 rel t426 [293,864,609,1082,377,629,1232,1184,1123] :=
  .mul [235,1179,559,627,1142,1170,46,816] c4 c415 (of_decide_eq_true rfl)
def t427 : Term := .add t425 t426
private theorem c427 : Value 1319 rel t427 [817,131,113,107,538,454,967,477,102] :=
  .add c425 c426 (of_decide_eq_true rfl)
def t428 : Term := .raw [865,269,714,351,260,300,538,135,169]
private theorem c428 : Value 1319 rel t428 [865,269,714,351,260,300,538,135,169] := .raw [865,269,714,351,260,300,538,135,169]
def t429 : Term := .mul t427 t428
private theorem c429 : Value 1319 rel t429 [1] :=
  .mul [879,472,688,903,135,236,632,91] c427 c428 (of_decide_eq_true rfl)
def t430 : Term := .mul t5 t374
private theorem c430 : Value 1319 rel t430 [290,1019,292,421,682,859,318,508,33] :=
  .mul [74,543,1247,193,12,987,1120,878,304,248,1230,1136,300] c5 c374 (of_decide_eq_true rfl)
def t431 : Term := .add t375 t430
private theorem c431 : Value 1319 rel t431 [273,124,675,760,1150,16,122,865,192,379,1112,220,137,1154,891] :=
  .add c375 c430 (of_decide_eq_true rfl)
def t432 : Term := .mul t5 t431
private theorem c432 : Value 1319 rel t432 [637,1162,547,145,1296,554,202,547,811] :=
  .mul [638,123,1183,1068,740,1143,810,391,771,133,537,1057,460,300] c5 c431 (of_decide_eq_true rfl)
def t433 : Term := .add t378 t432
private theorem c433 : Value 1319 rel t433 [506,768,725,1166,556,1172,557,1314,76,715,1239,440,564,353,258] :=
  .add c378 c432 (of_decide_eq_true rfl)
def t434 : Term := .mul t5 t433
private theorem c434 : Value 1319 rel t434 [572,1241,568,482,1014,366,742,1123,217] :=
  .mul [1250,565,1246,809,1281,375,675,919,1157,718,366,1144,128,793] c5 c433 (of_decide_eq_true rfl)
def t435 : Term := .add t381 t434
private theorem c435 : Value 1319 rel t435 [521,260,449,724,1147,250,411,1033,965,74,539,433,8,59,90] :=
  .add c381 c434 (of_decide_eq_true rfl)
def t436 : Term := .raw [863,1313,803,662,832,147,560,249,1282]
private theorem c436 : Value 1319 rel t436 [863,1313,803,662,832,147,560,249,1282] := .raw [863,1313,803,662,832,147,560,249,1282]
def t437 : Term := .mul t435 t436
private theorem c437 : Value 1319 rel t437 [1] :=
  .mul [507,643,242,300,911,992,966,315,1164,477,594,79,290,627] c435 c436 (of_decide_eq_true rfl)
def t438 : Term := .mul t5 t403
private theorem c438 : Value 1319 rel t438 [938,1020,1097,894,886,262,441,1258,1225] :=
  .mul [1212,1056,1083,1014,193,444,316,387] c5 c403 (of_decide_eq_true rfl)
def t439 : Term := .add t413 t438
private theorem c439 : Value 1319 rel t439 [1195,767,1151,343,997,767,1209,280,674] :=
  .add c413 c438 (of_decide_eq_true rfl)
def t440 : Term := .mul t5 t439
private theorem c440 : Value 1319 rel t440 [1189,28,0,466,588,596,611,885,752] :=
  .mul [774,929,485,1220,865,162,178,1315] c5 c439 (of_decide_eq_true rfl)
def t441 : Term := .add t425 t440
private theorem c441 : Value 1319 rel t441 [394,614,823,810,749,421,346,178,1050] :=
  .add c425 c440 (of_decide_eq_true rfl)
def t442 : Term := .raw [6,1069,638,908,843,761,521,75,695]
private theorem c442 : Value 1319 rel t442 [6,1069,638,908,843,761,521,75,695] := .raw [6,1069,638,908,843,761,521,75,695]
def t443 : Term := .mul t441 t442
private theorem c443 : Value 1319 rel t443 [1] :=
  .mul [510,470,5,81,1161,1151,370,343] c441 c442 (of_decide_eq_true rfl)
def t444 : Term := .raw [1116]
private theorem c444 : Value 1319 rel t444 [1116] := .raw [1116]
def t445 : Term := .raw [964,1116]
private theorem c445 : Value 1319 rel t445 [964,1116] := .raw [964,1116]
def t446 : Term := .mul t2 t444
private theorem c446 : Value 1319 rel t446 [1205,749,654,1279,1066,337,495,727,15] :=
  .mul [] c2 c444 (of_decide_eq_true rfl)
def t447 : Term := .add t445 t446
private theorem c447 : Value 1319 rel t447 [850,546,654,1279,1066,337,495,727,15] :=
  .add c445 c446 (of_decide_eq_true rfl)
def t448 : Term := .raw [251,203]
private theorem c448 : Value 1319 rel t448 [251,203] := .raw [251,203]
def t449 : Term := .mul t2 t447
private theorem c449 : Value 1319 rel t449 [833,879,371,992,1190,536,545,469,1000] :=
  .mul [1227,813,225,249,54,379,884,1032] c2 c447 (of_decide_eq_true rfl)
def t450 : Term := .add t448 t449
private theorem c450 : Value 1319 rel t450 [1084,1082,371,992,1190,536,545,469,1000] :=
  .add c448 c449 (of_decide_eq_true rfl)
def t451 : Term := .raw [813,970]
private theorem c451 : Value 1319 rel t451 [813,970] := .raw [813,970]
def t452 : Term := .mul t2 t450
private theorem c452 : Value 1319 rel t452 [858,338,918,669,830,561,324,681,721] :=
  .mul [828,472,968,1302,1313,452,1258,212] c2 c450 (of_decide_eq_true rfl)
def t453 : Term := .add t451 t452
private theorem c453 : Value 1319 rel t453 [352,1308,918,669,830,561,324,681,721] :=
  .add c451 c452 (of_decide_eq_true rfl)
def t454 : Term := .raw [440,1116]
private theorem c454 : Value 1319 rel t454 [440,1116] := .raw [440,1116]
def t455 : Term := .raw [387,85,1116]
private theorem c455 : Value 1319 rel t455 [387,85,1116] := .raw [387,85,1116]
def t456 : Term := .mul t2 t454
private theorem c456 : Value 1319 rel t456 [1084,75,660,777,291,203,1106,177,1138] :=
  .mul [15] c2 c454 (of_decide_eq_true rfl)
def t457 : Term := .add t455 t456
private theorem c457 : Value 1319 rel t457 [152,160,457,777,291,203,1106,177,1138] :=
  .add c455 c456 (of_decide_eq_true rfl)
def t458 : Term := .raw [910,938,203]
private theorem c458 : Value 1319 rel t458 [910,938,203] := .raw [910,938,203]
def t459 : Term := .mul t2 t457
private theorem c459 : Value 1319 rel t459 [181,951,1026,910,911,867,1193,271,450] :=
  .mul [1152,1307,744,579,802,375,1183,1001] c2 c457 (of_decide_eq_true rfl)
def t460 : Term := .add t458 t459
private theorem c460 : Value 1319 rel t460 [1091,570,1229,910,911,867,1193,271,450] :=
  .add c458 c459 (of_decide_eq_true rfl)
def t461 : Term := .raw [1239,1151,970]
private theorem c461 : Value 1319 rel t461 [1239,1151,970] := .raw [1239,1151,970]
def t462 : Term := .mul t2 t460
private theorem c462 : Value 1319 rel t462 [68,131,343,542,375,1041,38,561,212] :=
  .mul [1036,471,643,979,284,435,549,623] c2 c460 (of_decide_eq_true rfl)
def t463 : Term := .add t461 t462
private theorem c463 : Value 1319 rel t463 [1307,1282,1313,542,375,1041,38,561,212] :=
  .add c461 c462 (of_decide_eq_true rfl)
def t464 : Term := .mul t3 t453
private theorem c464 : Value 1319 rel t464 [394,1290,565,1223,479,316,1301,643,865] :=
  .mul [1094,162,838,113,432,722,446,987] c3 c453 (of_decide_eq_true rfl)
def t465 : Term := .add t463 t464
private theorem c465 : Value 1319 rel t465 [382,1253,559,446,854,38,20,1204,1077] :=
  .add c463 c464 (of_decide_eq_true rfl)
def t466 : Term := .raw [742,1177]
private theorem c466 : Value 1319 rel t466 [742,1177] := .raw [742,1177]
def t467 : Term := .raw [56,827,1177]
private theorem c467 : Value 1319 rel t467 [56,827,1177] := .raw [56,827,1177]
def t468 : Term := .mul t2 t466
private theorem c468 : Value 1319 rel t468 [563,746,307,66,1035,954,1225,595,1261] :=
  .mul [1310] c2 c466 (of_decide_eq_true rfl)
def t469 : Term := .add t467 t468
private theorem c469 : Value 1319 rel t469 [619,254,165,66,1035,954,1225,595,1261] :=
  .add c467 c468 (of_decide_eq_true rfl)
def t470 : Term := .raw [581,884,14]
private theorem c470 : Value 1319 rel t470 [581,884,14] := .raw [581,884,14]
def t471 : Term := .mul t2 t469
private theorem c471 : Value 1319 rel t471 [88,846,732,317,799,611,369,1014,884] :=
  .mul [511,316,484,633,27,15,956,758] c2 c469 (of_decide_eq_true rfl)
def t472 : Term := .add t470 t471
private theorem c472 : Value 1319 rel t472 [669,411,746,317,799,611,369,1014,884] :=
  .add c470 c471 (of_decide_eq_true rfl)
def t473 : Term := .raw [1076,502,801]
private theorem c473 : Value 1319 rel t473 [1076,502,801] := .raw [1076,502,801]
def t474 : Term := .mul t2 t472
private theorem c474 : Value 1319 rel t474 [309,43,45,208,583,1137,358,272,576] :=
  .mul [723,59,365,547,41,223,1002,409] c2 c472 (of_decide_eq_true rfl)
def t475 : Term := .add t473 t474
private theorem c475 : Value 1319 rel t475 [66,545,846,208,583,1137,358,272,576] :=
  .add c473 c474 (of_decide_eq_true rfl)
def t476 : Term := .mul t3 t465
private theorem c476 : Value 1319 rel t476 [1029,676,425,1080,945,406,1268,665,1252] :=
  .mul [816,980,79,245,668,461,120,1167] c3 c465 (of_decide_eq_true rfl)
def t477 : Term := .add t475 t476
private theorem c477 : Value 1319 rel t477 [1095,1221,1271,1288,209,224,307,937,509] :=
  .add c475 c476 (of_decide_eq_true rfl)
def t478 : Term := .raw [114]
private theorem c478 : Value 1319 rel t478 [114] := .raw [114]
def t479 : Term := .raw [1052,114]
private theorem c479 : Value 1319 rel t479 [1052,114] := .raw [1052,114]
def t480 : Term := .mul t2 t478
private theorem c480 : Value 1319 rel t480 [116,580,237,1244,350,467,1093,209,193] :=
  .mul [] c2 c478 (of_decide_eq_true rfl)
def t481 : Term := .add t479 t480
private theorem c481 : Value 1319 rel t481 [1168,694,237,1244,350,467,1093,209,193] :=
  .add c479 c480 (of_decide_eq_true rfl)
def t482 : Term := .raw [1086,1109]
private theorem c482 : Value 1319 rel t482 [1086,1109] := .raw [1086,1109]
def t483 : Term := .mul t2 t481
private theorem c483 : Value 1319 rel t483 [258,75,1251,743,739,820,6,1198,810] :=
  .mul [487,700,257,302,431,216,998,616] c2 c481 (of_decide_eq_true rfl)
def t484 : Term := .add t482 t483
private theorem c484 : Value 1319 rel t484 [25,1184,1251,743,739,820,6,1198,810] :=
  .add c482 c483 (of_decide_eq_true rfl)
def t485 : Term := .raw [1114,841]
private theorem c485 : Value 1319 rel t485 [1114,841] := .raw [1114,841]
def t486 : Term := .mul t2 t484
private theorem c486 : Value 1319 rel t486 [669,1054,1252,1005,196,388,1060,1240,341] :=
  .mul [830,1198,349,920,1101,978,1258,330] c2 c484 (of_decide_eq_true rfl)
def t487 : Term := .add t485 t486
private theorem c487 : Value 1319 rel t487 [464,576,1252,1005,196,388,1060,1240,341] :=
  .add c485 c486 (of_decide_eq_true rfl)
def t488 : Term := .raw [887,114]
private theorem c488 : Value 1319 rel t488 [887,114] := .raw [887,114]
def t489 : Term := .raw [626,620,114]
private theorem c489 : Value 1319 rel t489 [626,620,114] := .raw [626,620,114]
def t490 : Term := .mul t2 t488
private theorem c490 : Value 1319 rel t490 [927,54,1054,557,843,1297,1112,1160,266] :=
  .mul [193] c2 c488 (of_decide_eq_true rfl)
def t491 : Term := .add t489 t490
private theorem c491 : Value 1319 rel t491 [234,674,1168,557,843,1297,1112,1160,266] :=
  .add c489 c490 (of_decide_eq_true rfl)
def t492 : Term := .raw [1178,1255,1109]
private theorem c492 : Value 1319 rel t492 [1178,1255,1109] := .raw [1178,1255,1109]
def t493 : Term := .mul t2 t491
private theorem c493 : Value 1319 rel t493 [210,1053,1158,1218,158,333,973,648,553] :=
  .mul [64,902,748,385,1177,83,820,890] c2 c491 (of_decide_eq_true rfl)
def t494 : Term := .add t492 t493
private theorem c494 : Value 1319 rel t494 [69,989,948,1218,158,333,973,648,553] :=
  .add c492 c493 (of_decide_eq_true rfl)
def t495 : Term := .raw [511,1108,841]
private theorem c495 : Value 1319 rel t495 [511,1108,841] := .raw [511,1108,841]
def t496 : Term := .mul t2 t494
private theorem c496 : Value 1319 rel t496 [464,1226,1202,513,201,660,1318,92,909] :=
  .mul [363,116,408,713,105,1194,580,323] c2 c494 (of_decide_eq_true rfl)
def t497 : Term := .add t495 t496
private theorem c497 : Value 1319 rel t497 [975,1015,724,513,201,660,1318,92,909] :=
  .add c495 c496 (of_decide_eq_true rfl)
def t498 : Term := .mul t3 t487
private theorem c498 : Value 1319 rel t498 [982,23,926,820,830,964,73,518,497] :=
  .mul [835,1047,632,197,676,557,285,454] c3 c487 (of_decide_eq_true rfl)
def t499 : Term := .add t497 t498
private theorem c499 : Value 1319 rel t499 [638,1038,331,14,1031,305,72,610,87] :=
  .add c497 c498 (of_decide_eq_true rfl)
def t500 : Term := .raw [234,149]
private theorem c500 : Value 1319 rel t500 [234,149] := .raw [234,149]
def t501 : Term := .raw [432,1074,149]
private theorem c501 : Value 1319 rel t501 [432,1074,149] := .raw [432,1074,149]
def t502 : Term := .mul t2 t500
private theorem c502 : Value 1319 rel t502 [634,966,814,543,1082,589,227,458,997] :=
  .mul [1282] c2 c500 (of_decide_eq_true rfl)
def t503 : Term := .add t501 t502
private theorem c503 : Value 1319 rel t503 [1066,721,963,543,1082,589,227,458,997] :=
  .add c501 c502 (of_decide_eq_true rfl)
def t504 : Term := .raw [550,868,255]
private theorem c504 : Value 1319 rel t504 [550,868,255] := .raw [550,868,255]
def t505 : Term := .mul t2 t503
private theorem c505 : Value 1319 rel t505 [320,704,1072,709,850,429,1310,844,1136] :=
  .mul [643,1255,883,1186,74,950,198,797] c2 c503 (of_decide_eq_true rfl)
def t506 : Term := .add t504 t505
private theorem c506 : Value 1319 rel t506 [870,253,8,709,850,429,1310,844,1136] :=
  .add c504 c505 (of_decide_eq_true rfl)
def t507 : Term := .raw [211,37,0]
private theorem c507 : Value 1319 rel t507 [211,37,0] := .raw [211,37,0]
def t508 : Term := .mul t2 t506
private theorem c508 : Value 1319 rel t508 [278,360,17,218,903,1273,1014,384,186] :=
  .mul [627,979,850,484,477,871,2,72] c2 c506 (of_decide_eq_true rfl)
def t509 : Term := .add t507 t508
private theorem c509 : Value 1319 rel t509 [489,397,17,218,903,1273,1014,384,186] :=
  .add c507 c508 (of_decide_eq_true rfl)
def t510 : Term := .mul t3 t499
private theorem c510 : Value 1319 rel t510 [36,300,45,1044,383,636,1101,534,998] :=
  .mul [1070,593,1001,568,482,659,1117,785] c3 c499 (of_decide_eq_true rfl)
def t511 : Term := .add t509 t510
private theorem c511 : Value 1319 rel t511 [525,697,62,1262,1286,590,796,918,1184] :=
  .add c509 c510 (of_decide_eq_true rfl)
def t512 : Term := .mul t5 t477
private theorem c512 : Value 1319 rel t512 [1312,563,1116,414,136,133,1298,929,1199] :=
  .mul [19,156,483,189,76,1227,171,87] c5 c477 (of_decide_eq_true rfl)
def t513 : Term := .add t511 t512
private theorem c513 : Value 1319 rel t513 [518,1260,1178,357,103,723,775,528,1064] :=
  .add c511 c512 (of_decide_eq_true rfl)
def t514 : Term := .raw [233,511,779,797,270,116,541,978,42]
private theorem c514 : Value 1319 rel t514 [233,511,779,797,270,116,541,978,42] := .raw [233,511,779,797,270,116,541,978,42]
def t515 : Term := .mul t513 t514
private theorem c515 : Value 1319 rel t515 [1] :=
  .mul [855,480,745,756,376,89,92,1161] c513 c514 (of_decide_eq_true rfl)

def terminalExpression : Term := t373
theorem terminalProof : Value 1319 rel terminalExpression [1] := c373
def h1Expression : Term := t385
theorem h1Proof : Value 1319 rel h1Expression [1] := c385
def h2Expression : Term := t393
theorem h2Proof : Value 1319 rel h2Expression [1] := c393
def u2Expression : Term := t429
theorem u2Proof : Value 1319 rel u2Expression [1] := c429
def h3Expression : Term := t437
theorem h3Proof : Value 1319 rel h3Expression [1] := c437
def u3Expression : Term := t443
theorem u3Proof : Value 1319 rel u3Expression [1] := c443
def v3Expression : Term := t515
theorem v3Proof : Value 1319 rel v3Expression [1] := c515
def pencilExpression : List Term := [t13,t19,t25,t27,t1]
def splitExpression : List Term := [t38,t41,t42,t43,t1]
theorem splitProof : SameValues 1319 rel pencilExpression splitExpression :=
  .cons c13 c38 (.cons c19 c41 (.cons c25 c42 (.cons c27 c43 (.cons c1 c1 (.nil)))))

end RKCert.CompactResidue.Tape6
