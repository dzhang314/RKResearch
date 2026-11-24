module

public import RKCert.ERKCompactResidueCore

@[expose] public section

namespace RKCert.CompactResidue.Tape7
set_option maxHeartbeats 0

def rel : List Nat := [490,880,186,852,109,474,380,402,1307,942]

def t0 : Term := .raw []
private theorem c0 : Value 1319 rel t0 [] := .raw []
def t1 : Term := .raw [1]
private theorem c1 : Value 1319 rel t1 [1] := .raw [1]
def t2 : Term := .raw [342,1093,933,1,436,1155,401,194,151,52]
private theorem c2 : Value 1319 rel t2 [342,1093,933,1,436,1155,401,194,151,52] := .raw [342,1093,933,1,436,1155,401,194,151,52]
def t3 : Term := .raw [453,908,1100,447,1311,807,1095,710,998,345]
private theorem c3 : Value 1319 rel t3 [453,908,1100,447,1311,807,1095,710,998,345] := .raw [453,908,1100,447,1311,807,1095,710,998,345]
def t4 : Term := .raw [846,622,1164,796,310,131,490,1262,141,1089]
private theorem c4 : Value 1319 rel t4 [846,622,1164,796,310,131,490,1262,141,1089] := .raw [846,622,1164,796,310,131,490,1262,141,1089]
def t5 : Term := .raw [999,14,760,75,581,545,652,472,29,1152]
private theorem c5 : Value 1319 rel t5 [999,14,760,75,581,545,652,472,29,1152] := .raw [999,14,760,75,581,545,652,472,29,1152]
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
private theorem c28 : Value 1319 rel t28 [977,226,386,1318,883,164,918,1125,1168,1267] :=
  .neg c2 (of_decide_eq_true rfl)
def t29 : Term := .neg t3
private theorem c29 : Value 1319 rel t29 [866,411,219,872,8,512,224,609,321,974] :=
  .neg c3 (of_decide_eq_true rfl)
def t30 : Term := .neg t4
private theorem c30 : Value 1319 rel t30 [473,697,155,523,1009,1188,829,57,1178,230] :=
  .neg c4 (of_decide_eq_true rfl)
def t31 : Term := .neg t5
private theorem c31 : Value 1319 rel t31 [320,1305,559,1244,738,774,667,847,1290,167] :=
  .neg c5 (of_decide_eq_true rfl)
def t32 : Term := .mul t30 t31
private theorem c32 : Value 1319 rel t32 [1059,145,89,1279,237,1186,228,860,553,39] :=
  .mul [1198,710,885,371,951,752,436,851,159] c30 c31 (of_decide_eq_true rfl)
def t33 : Term := .add t30 t31
private theorem c33 : Value 1319 rel t33 [793,683,714,448,428,643,177,904,1149,397] :=
  .add c30 c31 (of_decide_eq_true rfl)
def t34 : Term := .mul t29 t32
private theorem c34 : Value 1319 rel t34 [270,181,634,320,791,641,959,887,192,1024] :=
  .mul [810,879,1250,370,163,1111,528,779,1054] c29 c32 (of_decide_eq_true rfl)
def t35 : Term := .mul t29 t33
private theorem c35 : Value 1319 rel t35 [574,74,644,891,609,1305,96,970,84,44] :=
  .mul [204,1269,1017,703,1257,119,23,1020,211] c29 c33 (of_decide_eq_true rfl)
def t36 : Term := .add t35 t32
private theorem c36 : Value 1319 rel t36 [314,219,733,851,846,1172,324,511,637,83] :=
  .add c35 c32 (of_decide_eq_true rfl)
def t37 : Term := .add t29 t33
private theorem c37 : Value 1319 rel t37 [340,1094,933,1,436,1155,401,194,151,52] :=
  .add c29 c33 (of_decide_eq_true rfl)
def t38 : Term := .mul t28 t34
private theorem c38 : Value 1319 rel t38 [1162,471] :=
  .mul [923,399,463,512,1290,948,89,902,831] c28 c34 (of_decide_eq_true rfl)
def t39 : Term := .mul t28 t36
private theorem c39 : Value 1319 rel t39 [609,856,685,999,528,678,360,432,1127,295] :=
  .mul [320,781,506,416,443,263,928,1313,960] c28 c36 (of_decide_eq_true rfl)
def t40 : Term := .mul t28 t37
private theorem c40 : Value 1319 rel t40 [127,439,586,468,473,147,995,808,682,1236] :=
  .mul [391,678,269,1080,271,321,973,1264,1253] c28 c37 (of_decide_eq_true rfl)
def t41 : Term := .add t39 t34
private theorem c41 : Value 1319 rel t41 [879,1037] :=
  .add c39 c34 (of_decide_eq_true rfl)
def t42 : Term := .add t40 t36
private theorem c42 : Value 1319 rel t42 [441,658] :=
  .add c40 c36 (of_decide_eq_true rfl)
def t43 : Term := .add t28 t37
private theorem c43 : Value 1319 rel t43 [1317,1] :=
  .add c28 c37 (of_decide_eq_true rfl)
def t44 : Term := .add t1 t31
private theorem c44 : Value 1319 rel t44 [321,1305,559,1244,738,774,667,847,1290,167] :=
  .add c1 c31 (of_decide_eq_true rfl)
def t45 : Term := .mul t10 t5
private theorem c45 : Value 1319 rel t45 [679,28,201,150,1162,1090,1304,944,58,985] :=
  .mul [] c10 c5 (of_decide_eq_true rfl)
def t46 : Term := .raw [3]
private theorem c46 : Value 1319 rel t46 [3] := .raw [3]
def t47 : Term := .mul t46 t3
private theorem c47 : Value 1319 rel t47 [40,86,662,22,1295,1102,647,811,356,1035] :=
  .mul [] c46 c3 (of_decide_eq_true rfl)
def t48 : Term := .neg t47
private theorem c48 : Value 1319 rel t48 [1279,1233,657,1297,24,217,672,508,963,284] :=
  .neg c47 (of_decide_eq_true rfl)
def t49 : Term := .add t45 t48
private theorem c49 : Value 1319 rel t49 [639,1261,858,128,1186,1307,657,133,1021,1269] :=
  .add c45 c48 (of_decide_eq_true rfl)
def t50 : Term := .add t49 t1
private theorem c50 : Value 1319 rel t50 [640,1261,858,128,1186,1307,657,133,1021,1269] :=
  .add c49 c1 (of_decide_eq_true rfl)
def t51 : Term := .mul t44 t50
private theorem c51 : Value 1319 rel t51 [194,705,1015,925,1251,152,1183,1034,557,867] :=
  .mul [1207,1236,776,1047,906,624,1086,1303,883] c44 c50 (of_decide_eq_true rfl)
def t52 : Term := .mul t3 t3
private theorem c52 : Value 1319 rel t52 [103,46,806,516,460,15,776,329,550,733] :=
  .mul [642,743,683,150,236,321,502,57,315] c3 c3 (of_decide_eq_true rfl)
def t53 : Term := .mul t52 t3
private theorem c53 : Value 1319 rel t53 [859,747,178,225,981,857,83,579,300,932] :=
  .mul [741,39,1107,711,887,533,237,297,956] c52 c3 (of_decide_eq_true rfl)
def t54 : Term := .neg t20
private theorem c54 : Value 1319 rel t54 [1193] :=
  .neg c20 (of_decide_eq_true rfl)
def t55 : Term := .mul t54 t52
private theorem c55 : Value 1319 rel t55 [212,799,7,934,76,748,1149,754,607,1291] :=
  .mul [] c54 c52 (of_decide_eq_true rfl)
def t56 : Term := .mul t14 t3
private theorem c56 : Value 1319 rel t56 [720,229,45,396,887,51,1094,89,1132,164] :=
  .mul [] c14 c3 (of_decide_eq_true rfl)
def t57 : Term := .add t55 t56
private theorem c57 : Value 1319 rel t57 [932,1028,52,11,963,799,924,843,420,136] :=
  .add c55 c56 (of_decide_eq_true rfl)
def t58 : Term := .neg t8
private theorem c58 : Value 1319 rel t58 [1313] :=
  .neg c8 (of_decide_eq_true rfl)
def t59 : Term := .add t57 t58
private theorem c59 : Value 1319 rel t59 [926,1028,52,11,963,799,924,843,420,136] :=
  .add c57 c58 (of_decide_eq_true rfl)
def t60 : Term := .mul t59 t7
private theorem c60 : Value 1319 rel t60 [1173,1080,1194,1115,247,1250,11,434,5,1195] :=
  .mul [] c59 c7 (of_decide_eq_true rfl)
def t61 : Term := .add t53 t60
private theorem c61 : Value 1319 rel t61 [713,508,53,21,1228,788,94,1013,305,808] :=
  .add c53 c60 (of_decide_eq_true rfl)
def t62 : Term := .mul t51 t61
private theorem c62 : Value 1319 rel t62 [411,1296,1092,1292,514,74,483,724,609,443] :=
  .mul [658,1306,150,149,220,806,89,891,147] c51 c61 (of_decide_eq_true rfl)
def t63 : Term := .mul t4 t4
private theorem c63 : Value 1319 rel t63 [101,1031,816,963,610,935,493,1142,1265,555] :=
  .mul [868,1025,818,1184,823,410,1118,1070,140] c4 c4 (of_decide_eq_true rfl)
def t64 : Term := .mul t46 t63
private theorem c64 : Value 1319 rel t64 [303,455,1129,251,511,167,160,788,1157,346] :=
  .mul [] c46 c63 (of_decide_eq_true rfl)
def t65 : Term := .mul t5 t5
private theorem c65 : Value 1319 rel t65 [99,1069,1269,697,243,867,54,469,773,176] :=
  .mul [623,191,1021,714,849,1163,446,462,190] c5 c5 (of_decide_eq_true rfl)
def t66 : Term := .mul t8 t65
private theorem c66 : Value 1319 rel t66 [594,1138,1019,225,139,1245,324,176,681,1056] :=
  .mul [] c8 c65 (of_decide_eq_true rfl)
def t67 : Term := .neg t66
private theorem c67 : Value 1319 rel t67 [725,181,300,1094,1180,74,995,1143,638,263] :=
  .neg c66 (of_decide_eq_true rfl)
def t68 : Term := .add t64 t67
private theorem c68 : Value 1319 rel t68 [1028,636,110,26,372,241,1155,612,476,609] :=
  .add c64 c67 (of_decide_eq_true rfl)
def t69 : Term := .mul t62 t68
private theorem c69 : Value 1319 rel t69 [736,905,480,610,216,868,437,87,1016,23] :=
  .mul [76,1111,135,977,531,993,20,1099,711] c62 c68 (of_decide_eq_true rfl)
def t70 : Term := .add t1 t29
private theorem c70 : Value 1319 rel t70 [867,411,219,872,8,512,224,609,321,974] :=
  .add c1 c29 (of_decide_eq_true rfl)
def t71 : Term := .mul t70 t70
private theorem c71 : Value 1319 rel t71 [517,868,1244,941,476,1039,1224,228,1192,43] :=
  .mul [642,743,683,150,236,321,502,57,315] c70 c70 (of_decide_eq_true rfl)
def t72 : Term := .mul t65 t5
private theorem c72 : Value 1319 rel t72 [63,624,416,896,114,396,631,824,843,614] :=
  .mul [1015,295,1184,303,1280,285,1148,1183,945] c65 c5 (of_decide_eq_true rfl)
def t73 : Term := .mul t54 t65
private theorem c73 : Value 1319 rel t73 [716,1163,1024,551,1038,235,1110,261,208,247] :=
  .mul [] c54 c65 (of_decide_eq_true rfl)
def t74 : Term := .mul t14 t5
private theorem c74 : Value 1319 rel t74 [1186,756,151,93,1037,412,914,427,247,215] :=
  .mul [] c14 c5 (of_decide_eq_true rfl)
def t75 : Term := .add t73 t74
private theorem c75 : Value 1319 rel t75 [583,600,1175,644,756,647,705,688,455,462] :=
  .add c73 c74 (of_decide_eq_true rfl)
def t76 : Term := .add t75 t58
private theorem c76 : Value 1319 rel t76 [577,600,1175,644,756,647,705,688,455,462] :=
  .add c75 c58 (of_decide_eq_true rfl)
def t77 : Term := .mul t76 t7
private theorem c77 : Value 1319 rel t77 [211,384,752,887,9,1311,715,71,555,665] :=
  .mul [] c76 c7 (of_decide_eq_true rfl)
def t78 : Term := .add t72 t77
private theorem c78 : Value 1319 rel t78 [274,1008,1168,464,123,388,27,895,79,1279] :=
  .add c72 c77 (of_decide_eq_true rfl)
def t79 : Term := .mul t71 t78
private theorem c79 : Value 1319 rel t79 [474,545,876,1211,493,464,481,785,1116,476] :=
  .mul [724,401,47,909,811,207,771,55,918] c71 c78 (of_decide_eq_true rfl)
def t80 : Term := .mul t8 t52
private theorem c80 : Value 1319 rel t80 [618,276,879,458,122,90,699,655,662,441] :=
  .mul [] c8 c52 (of_decide_eq_true rfl)
def t81 : Term := .neg t80
private theorem c81 : Value 1319 rel t81 [701,1043,440,861,1197,1229,620,664,657,878] :=
  .neg c80 (of_decide_eq_true rfl)
def t82 : Term := .add t64 t81
private theorem c82 : Value 1319 rel t82 [1004,179,250,1112,389,77,780,133,495,1224] :=
  .add c64 c81 (of_decide_eq_true rfl)
def t83 : Term := .mul t79 t82
private theorem c83 : Value 1319 rel t83 [83,1225,1,290,1144,647,826,378,426,149] :=
  .mul [959,837,37,938,525,1189,865,203,945] c79 c82 (of_decide_eq_true rfl)
def t84 : Term := .neg t83
private theorem c84 : Value 1319 rel t84 [1236,94,1318,1029,175,672,493,941,893,1170] :=
  .neg c83 (of_decide_eq_true rfl)
def t85 : Term := .add t69 t84
private theorem c85 : Value 1319 rel t85 [653,999,479,320,391,221,930,1028,590,1193] :=
  .add c69 c84 (of_decide_eq_true rfl)
def t86 : Term := .mul t46 t4
private theorem c86 : Value 1319 rel t86 [1219,547,854,1069,930,393,151,1148,423,629] :=
  .mul [] c46 c4 (of_decide_eq_true rfl)
def t87 : Term := .mul t86 t5
private theorem c87 : Value 1319 rel t87 [539,435,267,1199,711,920,684,1261,340,117] :=
  .mul [956,811,17,1113,215,937,1308,1234,477] c86 c5 (of_decide_eq_true rfl)
def t88 : Term := .raw [4]
private theorem c88 : Value 1319 rel t88 [4] := .raw [4]
def t89 : Term := .mul t88 t65
private theorem c89 : Value 1319 rel t89 [396,319,1119,150,972,830,216,557,454,704] :=
  .mul [] c88 c65 (of_decide_eq_true rfl)
def t90 : Term := .neg t89
private theorem c90 : Value 1319 rel t90 [923,1000,200,1169,347,489,1103,762,865,615] :=
  .neg c89 (of_decide_eq_true rfl)
def t91 : Term := .add t87 t90
private theorem c91 : Value 1319 rel t91 [143,116,467,1049,1058,90,468,704,1205,732] :=
  .add c87 c90 (of_decide_eq_true rfl)
def t92 : Term := .mul t62 t91
private theorem c92 : Value 1319 rel t92 [1280,708,1051,779,1172,474,733,804,812,879] :=
  .mul [1059,542,1292,1309,744,535,296,368,1121] c62 c91 (of_decide_eq_true rfl)
def t93 : Term := .mul t86 t3
private theorem c93 : Value 1319 rel t93 [971,1264,1115,407,695,153,321,599,460,349] :=
  .mul [797,870,233,953,1167,45,729,833,689] c86 c3 (of_decide_eq_true rfl)
def t94 : Term := .mul t88 t52
private theorem c94 : Value 1319 rel t94 [412,184,586,745,521,60,466,1316,881,294] :=
  .mul [] c88 c52 (of_decide_eq_true rfl)
def t95 : Term := .neg t94
private theorem c95 : Value 1319 rel t95 [907,1135,733,574,798,1259,853,3,438,1025] :=
  .neg c94 (of_decide_eq_true rfl)
def t96 : Term := .add t93 t95
private theorem c96 : Value 1319 rel t96 [559,1080,529,981,174,93,1174,602,898,55] :=
  .add c93 c95 (of_decide_eq_true rfl)
def t97 : Term := .mul t79 t96
private theorem c97 : Value 1319 rel t97 [586,275,1127,577,741,95,35,1171,329,487] :=
  .mul [268,87,1094,1089,944,158,641,1015,1119] c79 c96 (of_decide_eq_true rfl)
def t98 : Term := .neg t97
private theorem c98 : Value 1319 rel t98 [733,1044,192,742,578,1224,1284,148,990,832] :=
  .neg c97 (of_decide_eq_true rfl)
def t99 : Term := .add t92 t98
private theorem c99 : Value 1319 rel t99 [694,433,1243,202,431,379,698,952,483,392] :=
  .add c92 c98 (of_decide_eq_true rfl)
def t100 : Term := .mul t64 t99
private theorem c100 : Value 1319 rel t100 [1270,902,189,752,1189,87,1222,722,83,860] :=
  .mul [1237,564,397,461,1308,708,685,1141,1094] c64 c99 (of_decide_eq_true rfl)
def t101 : Term := .neg t86
private theorem c101 : Value 1319 rel t101 [100,772,465,250,389,926,1168,171,896,690] :=
  .neg c86 (of_decide_eq_true rfl)
def t102 : Term := .mul t101 t85
private theorem c102 : Value 1319 rel t102 [1276,30,261,934,409,399,61,47,218,120] :=
  .mul [47,255,1045,1248,183,576,159,616,114] c101 c85 (of_decide_eq_true rfl)
def t103 : Term := .mul t88 t85
private theorem c103 : Value 1319 rel t103 [1293,39,597,1280,245,884,1082,155,1041,815] :=
  .mul [] c88 c85 (of_decide_eq_true rfl)
def t104 : Term := .mul t8 t99
private theorem c104 : Value 1319 rel t104 [207,1279,863,1212,1267,955,231,436,260,1033] :=
  .mul [] c8 c99 (of_decide_eq_true rfl)
def t105 : Term := .neg t104
private theorem c105 : Value 1319 rel t105 [1112,40,456,107,52,364,1088,883,1059,286] :=
  .neg c104 (of_decide_eq_true rfl)
def t106 : Term := .add t103 t105
private theorem c106 : Value 1319 rel t106 [1086,79,1053,68,297,1248,851,1038,781,1101] :=
  .add c103 c105 (of_decide_eq_true rfl)
def t107 : Term := .raw [5]
private theorem c107 : Value 1319 rel t107 [5] := .raw [5]
def t108 : Term := .mul t107 t5
private theorem c108 : Value 1319 rel t108 [1038,70,1162,375,267,87,622,1041,145,484] :=
  .mul [] c107 c5 (of_decide_eq_true rfl)
def t109 : Term := .mul t108 t3
private theorem c109 : Value 1319 rel t109 [812,22,922,699,128,994,1264,774,93,78] :=
  .mul [571,938,300,168,383,520,219,634,786] c108 c3 (of_decide_eq_true rfl)
def t110 : Term := .neg t109
private theorem c110 : Value 1319 rel t110 [507,1297,397,620,1191,325,55,545,1226,1241] :=
  .neg c109 (of_decide_eq_true rfl)
def t111 : Term := .add t89 t110
private theorem c111 : Value 1319 rel t111 [903,297,197,770,844,1155,271,1102,361,626] :=
  .add c89 c110 (of_decide_eq_true rfl)
def t112 : Term := .mul t10 t3
private theorem c112 : Value 1319 rel t112 [906,497,881,894,1303,295,871,101,677,690] :=
  .mul [] c10 c3 (of_decide_eq_true rfl)
def t113 : Term := .add t111 t112
private theorem c113 : Value 1319 rel t113 [490,794,1078,345,828,131,1142,1203,1038,1316] :=
  .add c111 c112 (of_decide_eq_true rfl)
def t114 : Term := .neg t1
private theorem c114 : Value 1319 rel t114 [1318] :=
  .neg c1 (of_decide_eq_true rfl)
def t115 : Term := .add t113 t114
private theorem c115 : Value 1319 rel t115 [489,794,1078,345,828,131,1142,1203,1038,1316] :=
  .add c113 c114 (of_decide_eq_true rfl)
def t116 : Term := .neg t115
private theorem c116 : Value 1319 rel t116 [830,525,241,974,491,1188,177,116,281,3] :=
  .neg c115 (of_decide_eq_true rfl)
def t117 : Term := .add t5 t29
private theorem c117 : Value 1319 rel t117 [546,425,979,947,589,1057,876,1081,350,807] :=
  .add c5 c29 (of_decide_eq_true rfl)
def t118 : Term := .mul t46 t117
private theorem c118 : Value 1319 rel t118 [319,1275,299,203,448,533,1309,605,1050,1102] :=
  .mul [] c46 c117 (of_decide_eq_true rfl)
def t119 : Term := .mul t26 t4
private theorem c119 : Value 1319 rel t119 [946,75,310,1046,699,1057,339,114,1037,460] :=
  .mul [] c26 c4 (of_decide_eq_true rfl)
def t120 : Term := .mul t116 t63
private theorem c120 : Value 1319 rel t120 [454,946,22,3,811,389,601,121,630,350] :=
  .mul [702,281,714,13,1124,343,1143,290,346] c116 c63 (of_decide_eq_true rfl)
def t121 : Term := .mul t116 t119
private theorem c121 : Value 1319 rel t121 [306,264,1078,1318,1273,793,531,999,216,785] :=
  .mul [514,451,1057,515,1026,1145,688,1216,61] c116 c119 (of_decide_eq_true rfl)
def t122 : Term := .mul t118 t63
private theorem c122 : Value 1319 rel t122 [104,585,419,10,697,1314,896,438,1146,603] :=
  .mul [1240,450,106,94,254,1005,569,976,913] c118 c63 (of_decide_eq_true rfl)
def t123 : Term := .mul t118 t119
private theorem c123 : Value 1319 rel t123 [864,339,377,1054,1287,1104,593,1314,240,464] :=
  .mul [1001,118,432,999,585,854,161,517,424] c118 c119 (of_decide_eq_true rfl)
def t124 : Term := .add t121 t122
private theorem c124 : Value 1319 rel t124 [410,849,178,9,651,788,108,118,43,69] :=
  .add c121 c122 (of_decide_eq_true rfl)
def t125 : Term := .add t116 t123
private theorem c125 : Value 1319 rel t125 [375,864,618,709,459,973,770,111,521,467] :=
  .add c116 c123 (of_decide_eq_true rfl)
def t126 : Term := .raw [42]
private theorem c126 : Value 1319 rel t126 [42] := .raw [42]
def t127 : Term := .mul t126 t7
private theorem c127 : Value 1319 rel t127 [660] :=
  .mul [] c126 c7 (of_decide_eq_true rfl)
def t128 : Term := .mul t127 t100
private theorem c128 : Value 1319 rel t128 [635,451,754,376,1254,703,611,361,701,430] :=
  .mul [] c127 c100 (of_decide_eq_true rfl)
def t129 : Term := .mul t16 t7
private theorem c129 : Value 1319 rel t129 [440] :=
  .mul [] c16 c7 (of_decide_eq_true rfl)
def t130 : Term := .mul t129 t102
private theorem c130 : Value 1319 rel t130 [865,10,87,751,576,133,460,895,952,40] :=
  .mul [] c129 c102 (of_decide_eq_true rfl)
def t131 : Term := .raw [21]
private theorem c131 : Value 1319 rel t131 [21] := .raw [21]
def t132 : Term := .mul t131 t7
private theorem c132 : Value 1319 rel t132 [330] :=
  .mul [] c131 c7 (of_decide_eq_true rfl)
def t133 : Term := .mul t132 t106
private theorem c133 : Value 1319 rel t133 [931,1009,593,17,404,312,1202,919,525,605] :=
  .mul [] c132 c106 (of_decide_eq_true rfl)
def t134 : Term := .mul t116 t128
private theorem c134 : Value 1319 rel t134 [565,122,1197,653,724,179,695,325,171,119] :=
  .mul [258,238,1251,715,466,30,416,647,1290] c116 c128 (of_decide_eq_true rfl)
def t135 : Term := .mul t116 t130
private theorem c135 : Value 1319 rel t135 [791,236,811,566,1212,169,954,1006,990,573] :=
  .mul [881,196,616,156,382,402,1233,512,120] c116 c130 (of_decide_eq_true rfl)
def t136 : Term := .mul t116 t133
private theorem c136 : Value 1319 rel t136 [71,149,1207,1046,84,287,1023,426,981,411] :=
  .mul [1010,955,1043,881,713,771,961,416,496] c116 c133 (of_decide_eq_true rfl)
def t137 : Term := .mul t118 t128
private theorem c137 : Value 1319 rel t137 [1152,1159,908,625,1233,657,362,1082,768,239] :=
  .mul [200,591,1125,427,141,338,466,110,339] c118 c128 (of_decide_eq_true rfl)
def t138 : Term := .mul t118 t130
private theorem c138 : Value 1319 rel t138 [962,383,1017,1094,874,1036,1295,204,454,1119] :=
  .mul [669,709,1108,1215,41,573,428,212,553] c118 c130 (of_decide_eq_true rfl)
def t139 : Term := .mul t118 t133
private theorem c139 : Value 1319 rel t139 [344,695,500,454,228,1103,416,1206,1136,161] :=
  .mul [1077,638,700,1153,1311,1135,763,609,615] c118 c133 (of_decide_eq_true rfl)
def t140 : Term := .add t135 t137
private theorem c140 : Value 1319 rel t140 [624,76,400,1191,1126,826,1316,769,439,812] :=
  .add c135 c137 (of_decide_eq_true rfl)
def t141 : Term := .add t136 t138
private theorem c141 : Value 1319 rel t141 [1033,532,905,821,958,4,999,630,116,211] :=
  .add c136 c138 (of_decide_eq_true rfl)
def t142 : Term := .mul t106 t120
private theorem c142 : Value 1319 rel t142 [187,294,1176,255,1313,788,838,627,710,281] :=
  .mul [402,802,452,798,326,1133,574,501,202] c106 c120 (of_decide_eq_true rfl)
def t143 : Term := .mul t106 t124
private theorem c143 : Value 1319 rel t143 [1244,1237,770,1265,487,514,1043,1102,588,694] :=
  .mul [1285,1058,1130,13,245,473,313,122,786] c106 c124 (of_decide_eq_true rfl)
def t144 : Term := .mul t106 t125
private theorem c144 : Value 1319 rel t144 [880,288,1159,597,1115,301,742,748,554,633] :=
  .mul [382,136,550,45,431,586,416,1139,1076] c106 c125 (of_decide_eq_true rfl)
def t145 : Term := .mul t106 t118
private theorem c145 : Value 1319 rel t145 [57,142,681,497,912,455,345,867,587,644] :=
  .mul [351,1233,162,655,1287,583,414,1117,1141] c106 c118 (of_decide_eq_true rfl)
def t146 : Term := .mul t118 t100
private theorem c146 : Value 1319 rel t146 [985,999,497,1250,1147,1314,724,845,217,478] :=
  .mul [400,1182,931,854,282,676,932,220,678] c118 c100 (of_decide_eq_true rfl)
def t147 : Term := .mul t118 t102
private theorem c147 : Value 1319 rel t147 [248,1149,413,644,1303,470,1247,612,43,719] :=
  .mul [688,808,686,1007,123,400,1284,636,340] c118 c102 (of_decide_eq_true rfl)
def t148 : Term := .mul t118 t106
private theorem c148 : Value 1319 rel t148 [57,142,681,497,912,455,345,867,587,644] :=
  .mul [351,1233,162,655,1287,583,414,1117,1141] c118 c106 (of_decide_eq_true rfl)
def t149 : Term := .neg t146
private theorem c149 : Value 1319 rel t149 [334,320,822,69,172,5,595,474,1102,841] :=
  .neg c146 (of_decide_eq_true rfl)
def t150 : Term := .neg t147
private theorem c150 : Value 1319 rel t150 [1071,170,906,675,16,849,72,707,1276,600] :=
  .neg c147 (of_decide_eq_true rfl)
def t151 : Term := .neg t148
private theorem c151 : Value 1319 rel t151 [1262,1177,638,822,407,864,974,452,732,675] :=
  .neg c148 (of_decide_eq_true rfl)
def t152 : Term := .add t143 t149
private theorem c152 : Value 1319 rel t152 [259,238,273,15,659,519,319,257,371,216] :=
  .add c143 c149 (of_decide_eq_true rfl)
def t153 : Term := .add t144 t150
private theorem c153 : Value 1319 rel t153 [632,458,746,1272,1131,1150,814,136,511,1233] :=
  .add c144 c150 (of_decide_eq_true rfl)
def t154 : Term := .add t145 t151
private theorem c154 : Value 1319 rel t154 [] :=
  .add c145 c151 (of_decide_eq_true rfl)
def t155 : Term := .mul t106 t142
private theorem c155 : Value 1319 rel t155 [1052,1023,362,28,1260,210,337,672,650,875] :=
  .mul [476,339,336,581,14,35,1243,1264,735] c106 c142 (of_decide_eq_true rfl)
def t156 : Term := .mul t106 t152
private theorem c156 : Value 1319 rel t156 [1267,666,91,1014,1139,687,32,1034,776,840] :=
  .mul [1294,438,941,453,54,369,313,519,396] c106 c152 (of_decide_eq_true rfl)
def t157 : Term := .mul t106 t153
private theorem c157 : Value 1319 rel t157 [629,1041,1144,1222,1224,901,628,756,710,888] :=
  .mul [73,1244,1094,496,383,1141,551,26,282] c106 c153 (of_decide_eq_true rfl)
def t158 : Term := .mul t106 t154
private theorem c158 : Value 1319 rel t158 [] :=
  .mul [] c106 c154 (of_decide_eq_true rfl)
def t159 : Term := .mul t153 t100
private theorem c159 : Value 1319 rel t159 [102,784,1212,635,1276,596,898,940,308,217] :=
  .mul [198,445,1303,917,805,497,977,269,1223] c153 c100 (of_decide_eq_true rfl)
def t160 : Term := .mul t153 t102
private theorem c160 : Value 1319 rel t160 [631,1054,727,321,939,183,1042,798,1108,151] :=
  .mul [1260,508,1200,440,796,648,1058,1273,232] c153 c102 (of_decide_eq_true rfl)
def t161 : Term := .mul t153 t106
private theorem c161 : Value 1319 rel t161 [629,1041,1144,1222,1224,901,628,756,710,888] :=
  .mul [73,1244,1094,496,383,1141,551,26,282] c153 c106 (of_decide_eq_true rfl)
def t162 : Term := .neg t159
private theorem c162 : Value 1319 rel t162 [1217,535,107,684,43,723,421,379,1011,1102] :=
  .neg c159 (of_decide_eq_true rfl)
def t163 : Term := .neg t160
private theorem c163 : Value 1319 rel t163 [688,265,592,998,380,1136,277,521,211,1168] :=
  .neg c160 (of_decide_eq_true rfl)
def t164 : Term := .neg t161
private theorem c164 : Value 1319 rel t164 [690,278,175,97,95,418,691,563,609,431] :=
  .neg c161 (of_decide_eq_true rfl)
def t165 : Term := .add t155 t162
private theorem c165 : Value 1319 rel t165 [950,239,469,712,1303,933,758,1051,342,658] :=
  .add c155 c162 (of_decide_eq_true rfl)
def t166 : Term := .add t156 t163
private theorem c166 : Value 1319 rel t166 [636,931,683,693,200,504,309,236,987,689] :=
  .add c156 c163 (of_decide_eq_true rfl)
def t167 : Term := .add t157 t164
private theorem c167 : Value 1319 rel t167 [] :=
  .add c157 c164 (of_decide_eq_true rfl)
def t168 : Term := .mul t106 t165
private theorem c168 : Value 1319 rel t168 [803,396,753,608,1277,80,1055,1074,310,597] :=
  .mul [1269,113,542,999,342,665,918,822,327] c106 c165 (of_decide_eq_true rfl)
def t169 : Term := .mul t106 t166
private theorem c169 : Value 1319 rel t169 [728,566,681,1032,268,470,921,516,1047,723] :=
  .mul [670,309,27,460,495,909,751,1272,164] c106 c166 (of_decide_eq_true rfl)
def t170 : Term := .mul t106 t167
private theorem c170 : Value 1319 rel t170 [] :=
  .mul [] c106 c167 (of_decide_eq_true rfl)
def t171 : Term := .mul t106 t158
private theorem c171 : Value 1319 rel t171 [] :=
  .mul [] c106 c158 (of_decide_eq_true rfl)
def t172 : Term := .mul t166 t100
private theorem c172 : Value 1319 rel t172 [1279,390,367,1111,851,927,960,255,1033,148] :=
  .mul [828,739,1233,546,1029,1018,502,752,309] c166 c100 (of_decide_eq_true rfl)
def t173 : Term := .mul t166 t102
private theorem c173 : Value 1319 rel t173 [66,1213,401,420,55,493,465,719,378,990] :=
  .mul [632,1026,1168,1143,304,595,141,1133,902] c166 c102 (of_decide_eq_true rfl)
def t174 : Term := .mul t166 t106
private theorem c174 : Value 1319 rel t174 [728,566,681,1032,268,470,921,516,1047,723] :=
  .mul [670,309,27,460,495,909,751,1272,164] c166 c106 (of_decide_eq_true rfl)
def t175 : Term := .neg t172
private theorem c175 : Value 1319 rel t175 [40,929,952,208,468,392,359,1064,286,1171] :=
  .neg c172 (of_decide_eq_true rfl)
def t176 : Term := .neg t173
private theorem c176 : Value 1319 rel t176 [1253,106,918,899,1264,826,854,600,941,329] :=
  .neg c173 (of_decide_eq_true rfl)
def t177 : Term := .neg t174
private theorem c177 : Value 1319 rel t177 [591,753,638,287,1051,849,398,803,272,596] :=
  .neg c174 (of_decide_eq_true rfl)
def t178 : Term := .add t168 t176
private theorem c178 : Value 1319 rel t178 [737,502,352,188,1222,906,590,355,1251,926] :=
  .add c168 c176 (of_decide_eq_true rfl)
def t179 : Term := .add t169 t177
private theorem c179 : Value 1319 rel t179 [] :=
  .add c169 c177 (of_decide_eq_true rfl)
def t180 : Term := .mul t106 t175
private theorem c180 : Value 1319 rel t180 [1202,714,725,404,369,941,737,841,1140,1018] :=
  .mul [969,745,440,1095,1162,1042,962,419,608] c106 c175 (of_decide_eq_true rfl)
def t181 : Term := .mul t106 t178
private theorem c181 : Value 1319 rel t181 [290,648,616,830,923,143,319,832,839,492] :=
  .mul [596,1207,32,47,1302,1288,834,1283,1258] c106 c178 (of_decide_eq_true rfl)
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
private theorem c185 : Value 1319 rel t185 [795,949,1028,671,768,843,144,951,1144,529] :=
  .mul [1039,983,182,362,954,380,623,334,1003] c178 c100 (of_decide_eq_true rfl)
def t186 : Term := .mul t178 t102
private theorem c186 : Value 1319 rel t186 [616,1127,246,851,239,665,430,680,1318,747] :=
  .mul [1000,1309,552,430,1053,487,847,334,324] c178 c102 (of_decide_eq_true rfl)
def t187 : Term := .mul t178 t106
private theorem c187 : Value 1319 rel t187 [290,648,616,830,923,143,319,832,839,492] :=
  .mul [596,1207,32,47,1302,1288,834,1283,1258] c178 c106 (of_decide_eq_true rfl)
def t188 : Term := .neg t185
private theorem c188 : Value 1319 rel t188 [524,370,291,648,551,476,1175,368,175,790] :=
  .neg c185 (of_decide_eq_true rfl)
def t189 : Term := .neg t186
private theorem c189 : Value 1319 rel t189 [703,192,1073,468,1080,654,889,639,1,572] :=
  .neg c186 (of_decide_eq_true rfl)
def t190 : Term := .neg t187
private theorem c190 : Value 1319 rel t190 [1029,671,703,489,396,1176,1000,487,480,827] :=
  .neg c187 (of_decide_eq_true rfl)
def t191 : Term := .add t180 t189
private theorem c191 : Value 1319 rel t191 [586,906,479,872,130,276,307,161,1141,271] :=
  .add c180 c189 (of_decide_eq_true rfl)
def t192 : Term := .add t181 t190
private theorem c192 : Value 1319 rel t192 [] :=
  .add c181 c190 (of_decide_eq_true rfl)
def t193 : Term := .mul t106 t134
private theorem c193 : Value 1319 rel t193 [1301,686,1129,514,882,1150,786,979,263,8] :=
  .mul [772,485,179,595,307,1193,1016,12,438] c106 c134 (of_decide_eq_true rfl)
def t194 : Term := .mul t106 t140
private theorem c194 : Value 1319 rel t194 [1291,564,665,918,691,703,1201,572,65,379] :=
  .mul [119,439,1060,1231,1306,211,706,545,1049] c106 c140 (of_decide_eq_true rfl)
def t195 : Term := .mul t106 t141
private theorem c195 : Value 1319 rel t195 [637,713,1072,658,144,226,825,606,1009,232] :=
  .mul [724,1108,266,113,1045,739,113,42,167] c106 c141 (of_decide_eq_true rfl)
def t196 : Term := .mul t106 t139
private theorem c196 : Value 1319 rel t196 [294,745,1037,1160,1084,1292,56,144,32,1139] :=
  .mul [288,1116,376,558,257,827,1312,498,515] c106 c139 (of_decide_eq_true rfl)
def t197 : Term := .mul t139 t100
private theorem c197 : Value 1319 rel t197 [611,614,197,32,926,638,1234,549,764,1147] :=
  .mul [216,1125,641,448,1133,817,182,1078,1284] c139 c100 (of_decide_eq_true rfl)
def t198 : Term := .mul t139 t102
private theorem c198 : Value 1319 rel t198 [21,507,1190,524,1216,1225,155,1055,500,859] :=
  .mul [469,873,72,1178,1202,288,230,1145,854] c139 c102 (of_decide_eq_true rfl)
def t199 : Term := .mul t139 t106
private theorem c199 : Value 1319 rel t199 [294,745,1037,1160,1084,1292,56,144,32,1139] :=
  .mul [288,1116,376,558,257,827,1312,498,515] c139 c106 (of_decide_eq_true rfl)
def t200 : Term := .neg t197
private theorem c200 : Value 1319 rel t200 [708,705,1122,1287,393,681,85,770,555,172] :=
  .neg c197 (of_decide_eq_true rfl)
def t201 : Term := .neg t198
private theorem c201 : Value 1319 rel t201 [1298,812,129,795,103,94,1164,264,819,460] :=
  .neg c198 (of_decide_eq_true rfl)
def t202 : Term := .neg t199
private theorem c202 : Value 1319 rel t202 [1025,574,282,159,235,27,1263,1175,1287,180] :=
  .neg c199 (of_decide_eq_true rfl)
def t203 : Term := .add t194 t200
private theorem c203 : Value 1319 rel t203 [680,1269,468,886,1084,65,1286,23,620,551] :=
  .add c194 c200 (of_decide_eq_true rfl)
def t204 : Term := .add t195 t201
private theorem c204 : Value 1319 rel t204 [616,206,1201,134,247,320,670,870,509,692] :=
  .add c195 c201 (of_decide_eq_true rfl)
def t205 : Term := .add t196 t202
private theorem c205 : Value 1319 rel t205 [] :=
  .add c196 c202 (of_decide_eq_true rfl)
def t206 : Term := .mul t106 t193
private theorem c206 : Value 1319 rel t206 [1141,1156,1092,1045,305,17,1164,591,1192,335] :=
  .mul [874,420,902,1092,542,87,911,981,894] c106 c193 (of_decide_eq_true rfl)
def t207 : Term := .mul t106 t203
private theorem c207 : Value 1319 rel t207 [613,1148,334,730,351,793,372,387,594,24] :=
  .mul [225,1263,18,1121,1092,1295,1304,293,1230] c106 c203 (of_decide_eq_true rfl)
def t208 : Term := .mul t106 t204
private theorem c208 : Value 1319 rel t208 [607,174,1274,427,306,630,208,1117,19,1178] :=
  .mul [1169,263,1049,274,1070,1061,893,885,829] c106 c204 (of_decide_eq_true rfl)
def t209 : Term := .mul t106 t205
private theorem c209 : Value 1319 rel t209 [] :=
  .mul [] c106 c205 (of_decide_eq_true rfl)
def t210 : Term := .mul t204 t100
private theorem c210 : Value 1319 rel t210 [31,401,58,119,756,1082,40,98,1078,812] :=
  .mul [775,707,1307,500,1022,961,1095,892,251] c204 c100 (of_decide_eq_true rfl)
def t211 : Term := .mul t204 t102
private theorem c211 : Value 1319 rel t211 [752,1252,634,1067,1196,275,755,7,384,270] :=
  .mul [1240,717,83,728,254,321,415,1281,1262] c204 c102 (of_decide_eq_true rfl)
def t212 : Term := .mul t204 t106
private theorem c212 : Value 1319 rel t212 [607,174,1274,427,306,630,208,1117,19,1178] :=
  .mul [1169,263,1049,274,1070,1061,893,885,829] c204 c106 (of_decide_eq_true rfl)
def t213 : Term := .neg t210
private theorem c213 : Value 1319 rel t213 [1288,918,1261,1200,563,237,1279,1221,241,507] :=
  .neg c210 (of_decide_eq_true rfl)
def t214 : Term := .neg t211
private theorem c214 : Value 1319 rel t214 [567,67,685,252,123,1044,564,1312,935,1049] :=
  .neg c211 (of_decide_eq_true rfl)
def t215 : Term := .neg t212
private theorem c215 : Value 1319 rel t215 [712,1145,45,892,1013,689,1111,202,1300,141] :=
  .neg c212 (of_decide_eq_true rfl)
def t216 : Term := .add t206 t213
private theorem c216 : Value 1319 rel t216 [1110,755,1034,926,868,254,1124,493,114,842] :=
  .add c206 c213 (of_decide_eq_true rfl)
def t217 : Term := .add t207 t214
private theorem c217 : Value 1319 rel t217 [1180,1215,1019,982,474,518,936,380,210,1073] :=
  .add c207 c214 (of_decide_eq_true rfl)
def t218 : Term := .add t208 t215
private theorem c218 : Value 1319 rel t218 [] :=
  .add c208 c215 (of_decide_eq_true rfl)
def t219 : Term := .mul t106 t216
private theorem c219 : Value 1319 rel t219 [605,1160,241,457,333,604,116,552,738,1124] :=
  .mul [381,50,1067,428,253,684,0,226,1104] c106 c216 (of_decide_eq_true rfl)
def t220 : Term := .mul t106 t217
private theorem c220 : Value 1319 rel t220 [236,1136,1022,1238,309,990,387,485,1052,414] :=
  .mul [820,1181,1094,615,291,607,530,709,868] c106 c217 (of_decide_eq_true rfl)
def t221 : Term := .mul t106 t218
private theorem c221 : Value 1319 rel t221 [] :=
  .mul [] c106 c218 (of_decide_eq_true rfl)
def t222 : Term := .mul t106 t209
private theorem c222 : Value 1319 rel t222 [] :=
  .mul [] c106 c209 (of_decide_eq_true rfl)
def t223 : Term := .mul t217 t100
private theorem c223 : Value 1319 rel t223 [444,873,1014,193,1168,941,962,798,214,877] :=
  .mul [22,948,797,698,418,874,998,92,799] c217 c100 (of_decide_eq_true rfl)
def t224 : Term := .mul t217 t102
private theorem c224 : Value 1319 rel t224 [378,819,256,1109,826,305,223,1157,478,63] :=
  .mul [1068,363,1035,291,280,1124,497,1227,817] c217 c102 (of_decide_eq_true rfl)
def t225 : Term := .mul t217 t106
private theorem c225 : Value 1319 rel t225 [236,1136,1022,1238,309,990,387,485,1052,414] :=
  .mul [820,1181,1094,615,291,607,530,709,868] c217 c106 (of_decide_eq_true rfl)
def t226 : Term := .neg t223
private theorem c226 : Value 1319 rel t226 [875,446,305,1126,151,378,357,521,1105,442] :=
  .neg c223 (of_decide_eq_true rfl)
def t227 : Term := .neg t224
private theorem c227 : Value 1319 rel t227 [941,500,1063,210,493,1014,1096,162,841,1256] :=
  .neg c224 (of_decide_eq_true rfl)
def t228 : Term := .neg t225
private theorem c228 : Value 1319 rel t228 [1083,183,297,81,1010,329,932,834,267,905] :=
  .neg c225 (of_decide_eq_true rfl)
def t229 : Term := .add t219 t227
private theorem c229 : Value 1319 rel t229 [227,341,1304,667,826,299,1212,714,260,1061] :=
  .add c219 c227 (of_decide_eq_true rfl)
def t230 : Term := .add t220 t228
private theorem c230 : Value 1319 rel t230 [] :=
  .add c220 c228 (of_decide_eq_true rfl)
def t231 : Term := .mul t106 t226
private theorem c231 : Value 1319 rel t231 [26,72,71,143,946,40,1095,709,481,660] :=
  .mul [688,1164,657,621,500,196,1072,1063,1250] c106 c226 (of_decide_eq_true rfl)
def t232 : Term := .mul t106 t229
private theorem c232 : Value 1319 rel t232 [113,283,862,940,1239,97,1154,400,337,546] :=
  .mul [1088,899,921,292,783,499,191,602,846] c106 c229 (of_decide_eq_true rfl)
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
private theorem c236 : Value 1319 rel t236 [561,214,726,810,840,1259,82,388,949,775] :=
  .mul [896,589,1117,873,188,1042,646,797,1031] c229 c100 (of_decide_eq_true rfl)
def t237 : Term := .mul t229 t102
private theorem c237 : Value 1319 rel t237 [75,424,752,890,171,1216,1090,847,120,257] :=
  .mul [440,80,1109,1026,19,236,142,106,696] c229 c102 (of_decide_eq_true rfl)
def t238 : Term := .mul t229 t106
private theorem c238 : Value 1319 rel t238 [113,283,862,940,1239,97,1154,400,337,546] :=
  .mul [1088,899,921,292,783,499,191,602,846] c229 c106 (of_decide_eq_true rfl)
def t239 : Term := .neg t236
private theorem c239 : Value 1319 rel t239 [758,1105,593,509,479,60,1237,931,370,544] :=
  .neg c236 (of_decide_eq_true rfl)
def t240 : Term := .neg t237
private theorem c240 : Value 1319 rel t240 [1244,895,567,429,1148,103,229,472,1199,1062] :=
  .neg c237 (of_decide_eq_true rfl)
def t241 : Term := .neg t238
private theorem c241 : Value 1319 rel t241 [1206,1036,457,379,80,1222,165,919,982,773] :=
  .neg c238 (of_decide_eq_true rfl)
def t242 : Term := .add t231 t240
private theorem c242 : Value 1319 rel t242 [1270,967,638,572,775,143,5,1181,361,403] :=
  .add c231 c240 (of_decide_eq_true rfl)
def t243 : Term := .add t232 t241
private theorem c243 : Value 1319 rel t243 [] :=
  .add c232 c241 (of_decide_eq_true rfl)
def t244 : Term := .mul t106 t13
private theorem c244 : Value 1319 rel t244 [684,657,843,914,1040,1077,164,665,1108,695] :=
  .mul [204] c106 c13 (of_decide_eq_true rfl)
def t245 : Term := .mul t106 t19
private theorem c245 : Value 1319 rel t245 [875,704,1238,308,874,522,464,298,330,680] :=
  .mul [802] c106 c19 (of_decide_eq_true rfl)
def t246 : Term := .mul t106 t25
private theorem c246 : Value 1319 rel t246 [760,453,774,345,324,1234,416,321,1276,344] :=
  .mul [327] c106 c25 (of_decide_eq_true rfl)
def t247 : Term := .mul t106 t27
private theorem c247 : Value 1319 rel t247 [485,343,952,1160,773,1308,1122,831,773,306] :=
  .mul [1101] c106 c27 (of_decide_eq_true rfl)
def t248 : Term := .neg t100
private theorem c248 : Value 1319 rel t248 [49,417,1130,567,130,1232,97,597,1236,459] :=
  .neg c100 (of_decide_eq_true rfl)
def t249 : Term := .neg t102
private theorem c249 : Value 1319 rel t249 [43,1289,1058,385,910,920,1258,1272,1101,1199] :=
  .neg c102 (of_decide_eq_true rfl)
def t250 : Term := .neg t106
private theorem c250 : Value 1319 rel t250 [233,1240,266,1251,1022,71,468,281,538,218] :=
  .neg c106 (of_decide_eq_true rfl)
def t251 : Term := .add t246 t248
private theorem c251 : Value 1319 rel t251 [809,870,585,912,454,1147,513,918,1193,803] :=
  .add c246 c248 (of_decide_eq_true rfl)
def t252 : Term := .add t247 t249
private theorem c252 : Value 1319 rel t252 [528,313,691,226,364,909,1061,784,555,186] :=
  .add c247 c249 (of_decide_eq_true rfl)
def t253 : Term := .add t106 t250
private theorem c253 : Value 1319 rel t253 [] :=
  .add c106 c250 (of_decide_eq_true rfl)
def t254 : Term := .mul t106 t244
private theorem c254 : Value 1319 rel t254 [699,969,232,136,825,468,1305,715,556,28] :=
  .mul [1110,994,646,423,575,685,400,494,175] c106 c244 (of_decide_eq_true rfl)
def t255 : Term := .mul t106 t245
private theorem c255 : Value 1319 rel t255 [1061,379,745,163,631,216,115,428,523,309] :=
  .mul [892,143,682,923,1294,459,964,578,807] c106 c245 (of_decide_eq_true rfl)
def t256 : Term := .mul t106 t251
private theorem c256 : Value 1319 rel t256 [58,1077,1076,963,950,387,1006,671,92,305] :=
  .mul [156,829,859,850,742,1165,330,899,373] c106 c251 (of_decide_eq_true rfl)
def t257 : Term := .mul t106 t252
private theorem c257 : Value 1319 rel t257 [329,476,624,891,318,1136,671,532,908,912] :=
  .mul [529,1007,48,1032,40,716,244,1239,341] c106 c252 (of_decide_eq_true rfl)
def t258 : Term := .mul t106 t253
private theorem c258 : Value 1319 rel t258 [] :=
  .mul [] c106 c253 (of_decide_eq_true rfl)
def t259 : Term := .mul t252 t100
private theorem c259 : Value 1319 rel t259 [1173,337,297,1181,974,413,61,114,809,187] :=
  .mul [284,725,1121,25,535,698,756,511,361] c252 c100 (of_decide_eq_true rfl)
def t260 : Term := .mul t252 t102
private theorem c260 : Value 1319 rel t260 [447,1117,346,613,668,625,633,811,120,905] :=
  .mul [1019,337,26,617,732,659,691,889,1216] c252 c102 (of_decide_eq_true rfl)
def t261 : Term := .mul t252 t106
private theorem c261 : Value 1319 rel t261 [329,476,624,891,318,1136,671,532,908,912] :=
  .mul [529,1007,48,1032,40,716,244,1239,341] c252 c106 (of_decide_eq_true rfl)
def t262 : Term := .neg t259
private theorem c262 : Value 1319 rel t262 [146,982,1022,138,345,906,1258,1205,510,1132] :=
  .neg c259 (of_decide_eq_true rfl)
def t263 : Term := .neg t260
private theorem c263 : Value 1319 rel t263 [872,202,973,706,651,694,686,508,1199,414] :=
  .neg c260 (of_decide_eq_true rfl)
def t264 : Term := .neg t261
private theorem c264 : Value 1319 rel t264 [990,843,695,428,1001,183,648,787,411,407] :=
  .neg c261 (of_decide_eq_true rfl)
def t265 : Term := .add t255 t262
private theorem c265 : Value 1319 rel t265 [1207,42,448,301,976,1122,54,314,1033,122] :=
  .add c255 c262 (of_decide_eq_true rfl)
def t266 : Term := .add t256 t263
private theorem c266 : Value 1319 rel t266 [930,1279,730,350,282,1081,373,1179,1291,719] :=
  .add c256 c263 (of_decide_eq_true rfl)
def t267 : Term := .add t257 t264
private theorem c267 : Value 1319 rel t267 [] :=
  .add c257 c264 (of_decide_eq_true rfl)
def t268 : Term := .mul t106 t254
private theorem c268 : Value 1319 rel t268 [119,388,1047,873,1275,284,631,753,434,1248] :=
  .mul [1264,593,869,698,994,652,1306,457,491] c106 c254 (of_decide_eq_true rfl)
def t269 : Term := .mul t106 t265
private theorem c269 : Value 1319 rel t269 [391,750,410,258,29,408,215,701,752,1070] :=
  .mul [1280,901,1041,709,582,883,543,323,1103] c106 c265 (of_decide_eq_true rfl)
def t270 : Term := .mul t106 t266
private theorem c270 : Value 1319 rel t270 [109,1178,1132,732,197,1191,235,437,219,353] :=
  .mul [359,610,1131,738,52,1072,749,1007,219] c106 c266 (of_decide_eq_true rfl)
def t271 : Term := .mul t106 t267
private theorem c271 : Value 1319 rel t271 [] :=
  .mul [] c106 c267 (of_decide_eq_true rfl)
def t272 : Term := .mul t106 t258
private theorem c272 : Value 1319 rel t272 [] :=
  .mul [] c106 c258 (of_decide_eq_true rfl)
def t273 : Term := .mul t266 t100
private theorem c273 : Value 1319 rel t273 [738,439,78,268,990,573,104,1276,95,1180] :=
  .mul [789,580,342,565,866,523,1224,588,1048] c266 c100 (of_decide_eq_true rfl)
def t274 : Term := .mul t266 t102
private theorem c274 : Value 1319 rel t274 [837,1049,478,1115,401,597,612,721,1180,823] :=
  .mul [156,924,120,600,552,219,1049,677,545] c266 c102 (of_decide_eq_true rfl)
def t275 : Term := .mul t266 t106
private theorem c275 : Value 1319 rel t275 [109,1178,1132,732,197,1191,235,437,219,353] :=
  .mul [359,610,1131,738,52,1072,749,1007,219] c266 c106 (of_decide_eq_true rfl)
def t276 : Term := .neg t273
private theorem c276 : Value 1319 rel t276 [581,880,1241,1051,329,746,1215,43,1224,139] :=
  .neg c273 (of_decide_eq_true rfl)
def t277 : Term := .neg t274
private theorem c277 : Value 1319 rel t277 [482,270,841,204,918,722,707,598,139,496] :=
  .neg c274 (of_decide_eq_true rfl)
def t278 : Term := .neg t275
private theorem c278 : Value 1319 rel t278 [1210,141,187,587,1122,128,1084,882,1100,966] :=
  .neg c275 (of_decide_eq_true rfl)
def t279 : Term := .add t268 t276
private theorem c279 : Value 1319 rel t279 [700,1268,969,605,285,1030,527,796,339,68] :=
  .add c268 c276 (of_decide_eq_true rfl)
def t280 : Term := .add t269 t277
private theorem c280 : Value 1319 rel t280 [873,1020,1251,462,947,1130,922,1299,891,247] :=
  .add c269 c277 (of_decide_eq_true rfl)
def t281 : Term := .add t270 t278
private theorem c281 : Value 1319 rel t281 [] :=
  .add c270 c278 (of_decide_eq_true rfl)
def t282 : Term := .mul t106 t279
private theorem c282 : Value 1319 rel t282 [137,849,825,1111,639,186,739,796,552,124] :=
  .mul [675,822,736,1258,1053,1207,104,355,1004] c106 c279 (of_decide_eq_true rfl)
def t283 : Term := .mul t106 t280
private theorem c283 : Value 1319 rel t283 [999,91,847,961,807,224,1148,227,841,970] :=
  .mul [8,1283,860,749,296,879,675,520,233] c106 c280 (of_decide_eq_true rfl)
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
private theorem c287 : Value 1319 rel t287 [866,376,173,886,894,1064,711,663,280,817] :=
  .mul [474,767,771,1146,68,113,883,63,61] c280 c100 (of_decide_eq_true rfl)
def t288 : Term := .mul t280 t102
private theorem c288 : Value 1319 rel t288 [801,618,448,306,668,702,690,1236,1067,777] :=
  .mul [159,204,1240,447,577,539,940,136,622] c280 c102 (of_decide_eq_true rfl)
def t289 : Term := .mul t280 t106
private theorem c289 : Value 1319 rel t289 [999,91,847,961,807,224,1148,227,841,970] :=
  .mul [8,1283,860,749,296,879,675,520,233] c280 c106 (of_decide_eq_true rfl)
def t290 : Term := .neg t287
private theorem c290 : Value 1319 rel t290 [453,943,1146,433,425,255,608,656,1039,502] :=
  .neg c287 (of_decide_eq_true rfl)
def t291 : Term := .neg t288
private theorem c291 : Value 1319 rel t291 [518,701,871,1013,651,617,629,83,252,542] :=
  .neg c288 (of_decide_eq_true rfl)
def t292 : Term := .neg t289
private theorem c292 : Value 1319 rel t292 [320,1228,472,358,512,1095,171,1092,478,349] :=
  .neg c289 (of_decide_eq_true rfl)
def t293 : Term := .add t282 t291
private theorem c293 : Value 1319 rel t293 [655,231,377,805,1290,803,49,879,804,666] :=
  .add c282 c291 (of_decide_eq_true rfl)
def t294 : Term := .add t283 t292
private theorem c294 : Value 1319 rel t294 [] :=
  .add c283 c292 (of_decide_eq_true rfl)
def t295 : Term := .mul t63 t4
private theorem c295 : Value 1319 rel t295 [75,1163,103,980,997,1131,492,190,970,1005] :=
  .mul [1169,342,1145,539,1068,717,960,1318,293] c63 c4 (of_decide_eq_true rfl)
def t296 : Term := .mul t295 t4
private theorem c296 : Value 1319 rel t296 [690,989,1030,543,435,968,546,704,240,1114] :=
  .mul [1164,791,1185,454,582,1082,269,241,994] c295 c4 (of_decide_eq_true rfl)
def t297 : Term := .raw [378]
private theorem c297 : Value 1319 rel t297 [378] := .raw [378]
def t298 : Term := .mul t297 t296
private theorem c298 : Value 1319 rel t298 [977,565,235,809,874,541,624,993,1028,331] :=
  .mul [] c297 c296 (of_decide_eq_true rfl)
def t299 : Term := .raw [882]
private theorem c299 : Value 1319 rel t299 [882] := .raw [882]
def t300 : Term := .mul t299 t295
private theorem c300 : Value 1319 rel t300 [200,903,1154,415,900,378,1312,67,828,42] :=
  .mul [] c299 c295 (of_decide_eq_true rfl)
def t301 : Term := .neg t300
private theorem c301 : Value 1319 rel t301 [1119,416,165,904,419,941,7,1252,491,1277] :=
  .neg c300 (of_decide_eq_true rfl)
def t302 : Term := .add t298 t301
private theorem c302 : Value 1319 rel t302 [777,981,400,394,1293,163,631,926,200,289] :=
  .add c298 c301 (of_decide_eq_true rfl)
def t303 : Term := .raw [753]
private theorem c303 : Value 1319 rel t303 [753] := .raw [753]
def t304 : Term := .mul t303 t63
private theorem c304 : Value 1319 rel t304 [870,771,1113,1008,318,1028,590,1257,227,1111] :=
  .mul [] c303 c63 (of_decide_eq_true rfl)
def t305 : Term := .add t302 t304
private theorem c305 : Value 1319 rel t305 [328,433,194,83,292,1191,1221,864,427,81] :=
  .add c302 c304 (of_decide_eq_true rfl)
def t306 : Term := .raw [280]
private theorem c306 : Value 1319 rel t306 [280] := .raw [280]
def t307 : Term := .mul t306 t4
private theorem c307 : Value 1319 rel t307 [779,52,127,1288,1065,1067,24,1187,1229,231] :=
  .mul [] c306 c4 (of_decide_eq_true rfl)
def t308 : Term := .neg t307
private theorem c308 : Value 1319 rel t308 [540,1267,1192,31,254,252,1295,132,90,1088] :=
  .neg c307 (of_decide_eq_true rfl)
def t309 : Term := .add t305 t308
private theorem c309 : Value 1319 rel t309 [868,381,67,114,546,124,1197,996,517,1169] :=
  .add c305 c308 (of_decide_eq_true rfl)
def t310 : Term := .raw [40]
private theorem c310 : Value 1319 rel t310 [40] := .raw [40]
def t311 : Term := .add t309 t310
private theorem c311 : Value 1319 rel t311 [908,381,67,114,546,124,1197,996,517,1169] :=
  .add c309 c310 (of_decide_eq_true rfl)
def t312 : Term := .mul t85 t85
private theorem c312 : Value 1319 rel t312 [190,352,567,1049,534,22,805,968,532,54] :=
  .mul [75,1155,647,1137,249,368,555,737,48] c85 c85 (of_decide_eq_true rfl)
def t313 : Term := .mul t311 t312
private theorem c313 : Value 1319 rel t313 [588,142,220,77,1317,1038,664,1047,1156,145] :=
  .mul [1205,794,433,890,547,430,667,1093,1133] c311 c312 (of_decide_eq_true rfl)
def t314 : Term := .mul t296 t4
private theorem c314 : Value 1319 rel t314 [1184,753,550,1005,20,1307,363,243,1282,312] :=
  .mul [760,842,128,704,809,1044,915,924,985] c296 c4 (of_decide_eq_true rfl)
def t315 : Term := .raw [949]
private theorem c315 : Value 1319 rel t315 [949] := .raw [949]
def t316 : Term := .mul t315 t314
private theorem c316 : Value 1319 rel t316 [1147,1018,945,108,514,483,228,1101,500,632] :=
  .mul [] c315 c314 (of_decide_eq_true rfl)
def t317 : Term := .raw [1205]
private theorem c317 : Value 1319 rel t317 [1205] := .raw [1205]
def t318 : Term := .mul t317 t296
private theorem c318 : Value 1319 rel t318 [480,688,1290,91,532,444,1068,203,339,947] :=
  .mul [] c317 c296 (of_decide_eq_true rfl)
def t319 : Term := .neg t318
private theorem c319 : Value 1319 rel t319 [839,631,29,1228,787,875,251,1116,980,372] :=
  .neg c318 (of_decide_eq_true rfl)
def t320 : Term := .add t316 t319
private theorem c320 : Value 1319 rel t320 [667,330,974,17,1301,39,479,898,161,1004] :=
  .add c316 c319 (of_decide_eq_true rfl)
def t321 : Term := .raw [1302]
private theorem c321 : Value 1319 rel t321 [1302] := .raw [1302]
def t322 : Term := .mul t321 t295
private theorem c322 : Value 1319 rel t322 [44,14,887,487,198,558,869,727,657,62] :=
  .mul [] c321 c295 (of_decide_eq_true rfl)
def t323 : Term := .add t320 t322
private theorem c323 : Value 1319 rel t323 [711,344,542,504,180,597,29,306,818,1066] :=
  .add c320 c322 (of_decide_eq_true rfl)
def t324 : Term := .raw [912]
private theorem c324 : Value 1319 rel t324 [912] := .raw [912]
def t325 : Term := .mul t324 t63
private theorem c325 : Value 1319 rel t325 [1101,1144,276,1121,1021,646,1156,813,874,983] :=
  .mul [] c324 c63 (of_decide_eq_true rfl)
def t326 : Term := .add t323 t325
private theorem c326 : Value 1319 rel t326 [493,169,818,306,1201,1243,1185,1119,373,730] :=
  .add c323 c325 (of_decide_eq_true rfl)
def t327 : Term := .raw [660]
private theorem c327 : Value 1319 rel t327 [660] := .raw [660]
def t328 : Term := .mul t327 t4
private theorem c328 : Value 1319 rel t328 [423,311,582,398,155,725,245,631,730,1204] :=
  .mul [] c327 c4 (of_decide_eq_true rfl)
def t329 : Term := .neg t328
private theorem c329 : Value 1319 rel t329 [896,1008,737,921,1164,594,1074,688,589,115] :=
  .neg c328 (of_decide_eq_true rfl)
def t330 : Term := .add t326 t329
private theorem c330 : Value 1319 rel t330 [70,1177,236,1227,1046,518,940,488,962,845] :=
  .add c326 c329 (of_decide_eq_true rfl)
def t331 : Term := .raw [120]
private theorem c331 : Value 1319 rel t331 [120] := .raw [120]
def t332 : Term := .add t330 t331
private theorem c332 : Value 1319 rel t332 [190,1177,236,1227,1046,518,940,488,962,845] :=
  .add c330 c331 (of_decide_eq_true rfl)
def t333 : Term := .mul t332 t85
private theorem c333 : Value 1319 rel t333 [660,842,906,1086,520,844,267,915,1292,890] :=
  .mul [125,139,560,353,412,653,1087,805,369] c332 c85 (of_decide_eq_true rfl)
def t334 : Term := .mul t333 t99
private theorem c334 : Value 1319 rel t334 [353,653,321,1054,561,277,489,661,919,347] :=
  .mul [70,1182,586,1019,676,666,471,126,664] c333 c99 (of_decide_eq_true rfl)
def t335 : Term := .neg t334
private theorem c335 : Value 1319 rel t335 [966,666,998,265,758,1042,830,658,400,972] :=
  .neg c334 (of_decide_eq_true rfl)
def t336 : Term := .add t313 t335
private theorem c336 : Value 1319 rel t336 [235,808,1218,342,756,761,175,386,237,1117] :=
  .add c313 c335 (of_decide_eq_true rfl)
def t337 : Term := .mul t314 t4
private theorem c337 : Value 1319 rel t337 [942,1082,245,975,723,512,1242,775,968,446] :=
  .mul [698,834,182,476,509,574,734,572,785] c314 c4 (of_decide_eq_true rfl)
def t338 : Term := .raw [8]
private theorem c338 : Value 1319 rel t338 [8] := .raw [8]
def t339 : Term := .mul t338 t337
private theorem c339 : Value 1319 rel t339 [941,742,641,1205,508,139,703,924,1149,930] :=
  .mul [] c338 c337 (of_decide_eq_true rfl)
def t340 : Term := .neg t316
private theorem c340 : Value 1319 rel t340 [172,301,374,1211,805,836,1091,218,819,687] :=
  .neg c316 (of_decide_eq_true rfl)
def t341 : Term := .add t339 t340
private theorem c341 : Value 1319 rel t341 [1113,1043,1015,1097,1313,975,475,1142,649,298] :=
  .add c339 c340 (of_decide_eq_true rfl)
def t342 : Term := .mul t315 t296
private theorem c342 : Value 1319 rel t342 [586,752,91,897,1287,608,1106,682,892,667] :=
  .mul [] c315 c296 (of_decide_eq_true rfl)
def t343 : Term := .neg t342
private theorem c343 : Value 1319 rel t343 [733,567,1228,422,32,711,213,637,427,652] :=
  .neg c342 (of_decide_eq_true rfl)
def t344 : Term := .add t341 t343
private theorem c344 : Value 1319 rel t344 [527,291,924,200,26,367,688,460,1076,950] :=
  .add c341 c343 (of_decide_eq_true rfl)
def t345 : Term := .raw [1201]
private theorem c345 : Value 1319 rel t345 [1201] := .raw [1201]
def t346 : Term := .mul t345 t295
private theorem c346 : Value 1319 rel t346 [383,1261,1036,432,1064,1080,1299,3,293,120] :=
  .mul [] c345 c295 (of_decide_eq_true rfl)
def t347 : Term := .add t344 t346
private theorem c347 : Value 1319 rel t347 [910,233,641,632,1090,128,668,463,50,1070] :=
  .add c344 c346 (of_decide_eq_true rfl)
def t348 : Term := .raw [144]
private theorem c348 : Value 1319 rel t348 [144] := .raw [144]
def t349 : Term := .mul t348 t63
private theorem c349 : Value 1319 rel t349 [35,736,113,177,786,102,1085,892,138,780] :=
  .mul [] c348 c63 (of_decide_eq_true rfl)
def t350 : Term := .neg t349
private theorem c350 : Value 1319 rel t350 [1284,583,1206,1142,533,1217,234,427,1181,539] :=
  .neg c349 (of_decide_eq_true rfl)
def t351 : Term := .add t347 t350
private theorem c351 : Value 1319 rel t351 [875,816,528,455,304,26,902,890,1231,290] :=
  .add c347 c350 (of_decide_eq_true rfl)
def t352 : Term := .raw [360]
private theorem c352 : Value 1319 rel t352 [360] := .raw [360]
def t353 : Term := .mul t352 t4
private theorem c353 : Value 1319 rel t353 [1190,1009,917,337,804,995,973,584,638,297] :=
  .mul [] c352 c4 (of_decide_eq_true rfl)
def t354 : Term := .neg t353
private theorem c354 : Value 1319 rel t354 [129,310,402,982,515,324,346,735,681,1022] :=
  .neg c353 (of_decide_eq_true rfl)
def t355 : Term := .add t351 t354
private theorem c355 : Value 1319 rel t355 [1004,1126,930,118,819,350,1248,306,593,1312] :=
  .add c351 c354 (of_decide_eq_true rfl)
def t356 : Term := .raw [90]
private theorem c356 : Value 1319 rel t356 [90] := .raw [90]
def t357 : Term := .add t355 t356
private theorem c357 : Value 1319 rel t357 [1094,1126,930,118,819,350,1248,306,593,1312] :=
  .add c355 c356 (of_decide_eq_true rfl)
def t358 : Term := .mul t99 t99
private theorem c358 : Value 1319 rel t358 [275,162,298,209,1140,1117,718,258,95,92] :=
  .mul [1303,493,1277,1048,845,24,115,590,660] c99 c99 (of_decide_eq_true rfl)
def t359 : Term := .mul t357 t358
private theorem c359 : Value 1319 rel t359 [857,1235,618,1265,91,580,704,289,268,721] :=
  .mul [268,996,659,1131,500,581,1296,1223,675] c357 c358 (of_decide_eq_true rfl)
def t360 : Term := .add t336 t359
private theorem c360 : Value 1319 rel t360 [1092,724,517,288,847,22,879,675,505,519] :=
  .add c336 c359 (of_decide_eq_true rfl)
def t361 : Term := .mul t188 t293
private theorem c361 : Value 1319 rel t361 [247,1256,61,955,781,737,167,987,910,824] :=
  .mul [934,1196,122,805,105,851,82,277,1178] c188 c293 (of_decide_eq_true rfl)
def t362 : Term := .mul t191 t290
private theorem c362 : Value 1319 rel t362 [489,534,998,1211,540,865,1272,1128,597,935] :=
  .mul [431,2,103,167,264,1264,50,1120,185] c191 c290 (of_decide_eq_true rfl)
def t363 : Term := .neg t362
private theorem c363 : Value 1319 rel t363 [830,785,321,108,779,454,47,191,722,384] :=
  .neg c362 (of_decide_eq_true rfl)
def t364 : Term := .add t361 t363
private theorem c364 : Value 1319 rel t364 [1077,722,382,1063,241,1191,214,1178,313,1208] :=
  .add c361 c363 (of_decide_eq_true rfl)
def t365 : Term := .mul t106 t364
private theorem c365 : Value 1319 rel t365 [832,1304,1014,444,1119,260,1109,744,1309,417] :=
  .mul [818,741,292,1283,26,135,704,275,456] c106 c364 (of_decide_eq_true rfl)
def t366 : Term := .mul t239 t293
private theorem c366 : Value 1319 rel t366 [1307,835,224,284,663,823,190,667,319,807] :=
  .mul [85,658,276,17,1082,958,965,991,898] c239 c293 (of_decide_eq_true rfl)
def t367 : Term := .mul t242 t290
private theorem c367 : Value 1319 rel t367 [597,1250,977,495,570,318,100,1219,1202,227] :=
  .mul [811,1235,739,917,513,256,552,288,499] c242 c290 (of_decide_eq_true rfl)
def t368 : Term := .neg t367
private theorem c368 : Value 1319 rel t368 [722,69,342,824,749,1001,1219,100,117,1092] :=
  .neg c367 (of_decide_eq_true rfl)
def t369 : Term := .add t366 t368
private theorem c369 : Value 1319 rel t369 [710,904,566,1108,93,505,90,767,436,580] :=
  .add c366 c368 (of_decide_eq_true rfl)
def t370 : Term := .mul t365 t369
private theorem c370 : Value 1319 rel t370 [464,960,840,241,221,441,1180,556,264,1072] :=
  .mul [179,1026,410,740,418,1078,605,516,483] c365 c369 (of_decide_eq_true rfl)
def t371 : Term := .mul t370 t360
private theorem c371 : Value 1319 rel t371 [753,288,648,493,37,398,972,1060,936,811] :=
  .mul [1269,1147,237,112,700,46,998,1011,1069] c370 c360 (of_decide_eq_true rfl)
def t372 : Term := .raw [970,1316,233,575,1245,875,521,384,395,485]
private theorem c372 : Value 1319 rel t372 [970,1316,233,575,1245,875,521,384,395,485] := .raw [970,1316,233,575,1245,875,521,384,395,485]
def t373 : Term := .mul t371 t372
private theorem c373 : Value 1319 rel t373 [1] :=
  .mul [181,668,670,987,831,266,1286,13,273] c371 c372 (of_decide_eq_true rfl)
def t374 : Term := .raw [996,390,644,587,149,349,1167,1078,1245,289,254,928,682,891]
private theorem c374 : Value 1319 rel t374 [996,390,644,587,149,349,1167,1078,1245,289,254,928,682,891] := .raw [996,390,644,587,149,349,1167,1078,1245,289,254,928,682,891]
def t375 : Term := .raw [1302,424,383,339,468,476,1123,357,159,379,1112,220,137,1154,891]
private theorem c375 : Value 1319 rel t375 [1302,424,383,339,468,476,1123,357,159,379,1112,220,137,1154,891] := .raw [1302,424,383,339,468,476,1123,357,159,379,1112,220,137,1154,891]
def t376 : Term := .mul t2 t374
private theorem c376 : Value 1319 rel t376 [1082,165,419,429,893,201,546,473,1294,275] :=
  .mul [1299,926,1275,809,669,1155,1146,467,403,973,34,207,167] c2 c374 (of_decide_eq_true rfl)
def t377 : Term := .add t375 t376
private theorem c377 : Value 1319 rel t377 [1065,589,802,768,42,677,350,830,134,654,1112,220,137,1154,891] :=
  .add c375 c376 (of_decide_eq_true rfl)
def t378 : Term := .raw [1188,925,178,1021,579,618,355,767,584,715,1239,440,564,353,258]
private theorem c378 : Value 1319 rel t378 [1188,925,178,1021,579,618,355,767,584,715,1239,440,564,353,258] := .raw [1188,925,178,1021,579,618,355,767,584,715,1239,440,564,353,258]
def t379 : Term := .mul t2 t377
private theorem c379 : Value 1319 rel t379 [1185,806,1031,726,979,293,178,1313,1124,917] :=
  .mul [1103,1218,566,1307,837,1032,779,470,655,342,1161,853,1009,167] c2 c377 (of_decide_eq_true rfl)
def t380 : Term := .add t378 t379
private theorem c380 : Value 1319 rel t380 [1054,412,1209,428,239,911,533,761,389,313,1239,440,564,353,258] :=
  .add c378 c379 (of_decide_eq_true rfl)
def t381 : Term := .raw [1268,338,1200,242,133,1203,988,1229,748,74,539,433,8,59,90]
private theorem c381 : Value 1319 rel t381 [1268,338,1200,242,133,1203,988,1229,748,74,539,433,8,59,90] := .raw [1268,338,1200,242,133,1203,988,1229,748,74,539,433,8,59,90]
def t382 : Term := .mul t2 t380
private theorem c382 : Value 1319 rel t382 [1140,445,454,7,1256,338,1127,938,667,940] :=
  .mul [941,165,213,37,472,944,784,298,590,575,664,736,1130,226] c2 c380 (of_decide_eq_true rfl)
def t383 : Term := .add t381 t382
private theorem c383 : Value 1319 rel t383 [1089,783,335,249,70,222,796,848,96,1014,539,433,8,59,90] :=
  .add c381 c382 (of_decide_eq_true rfl)
def t384 : Term := .raw [1296,878,140,1292,747,212,961,1315,514,800]
private theorem c384 : Value 1319 rel t384 [1296,878,140,1292,747,212,961,1315,514,800] := .raw [1296,878,140,1292,747,212,961,1315,514,800]
def t385 : Term := .mul t383 t384
private theorem c385 : Value 1319 rel t385 [1] :=
  .mul [288,575,1017,670,338,733,1065,356,1171,372,619,14,831,774] c383 c384 (of_decide_eq_true rfl)
def t386 : Term := .raw [867,1059,1253,121]
private theorem c386 : Value 1319 rel t386 [867,1059,1253,121] := .raw [867,1059,1253,121]
def t387 : Term := .raw [433,550,17,25,121]
private theorem c387 : Value 1319 rel t387 [433,550,17,25,121] := .raw [433,550,17,25,121]
def t388 : Term := .mul t4 t386
private theorem c388 : Value 1319 rel t388 [56,584,571,630,269,1317,1300,108,712,893] :=
  .mul [156,1169,1188] c4 c386 (of_decide_eq_true rfl)
def t389 : Term := .add t387 t388
private theorem c389 : Value 1319 rel t389 [489,1134,588,655,390,1317,1300,108,712,893] :=
  .add c387 c388 (of_decide_eq_true rfl)
def t390 : Term := .raw [1088,1228,460,773,811]
private theorem c390 : Value 1319 rel t390 [1088,1228,460,773,811] := .raw [1088,1228,460,773,811]
def t391 : Term := .mul t4 t389
private theorem c391 : Value 1319 rel t391 [44,1128,94,287,874,1178,813,4,1078,419] :=
  .mul [744,1272,299,346,192,1165,301,539,374] c4 c389 (of_decide_eq_true rfl)
def t392 : Term := .add t390 t391
private theorem c392 : Value 1319 rel t392 [1132,1037,554,1060,366,1178,813,4,1078,419] :=
  .add c390 c391 (of_decide_eq_true rfl)
def t393 : Term := .raw [674,862,828,204,926]
private theorem c393 : Value 1319 rel t393 [674,862,828,204,926] := .raw [674,862,828,204,926]
def t394 : Term := .mul t4 t392
private theorem c394 : Value 1319 rel t394 [323,1302,160,194,487,521,410,1226,69,812] :=
  .mul [660,1259,640,355,1252,297,335,710,1236] c4 c392 (of_decide_eq_true rfl)
def t395 : Term := .add t393 t394
private theorem c395 : Value 1319 rel t395 [997,845,988,398,94,521,410,1226,69,812] :=
  .add c393 c394 (of_decide_eq_true rfl)
def t396 : Term := .raw [979,117,238,1274,121]
private theorem c396 : Value 1319 rel t396 [979,117,238,1274,121] := .raw [979,117,238,1274,121]
def t397 : Term := .raw [1118,273,990,1305,46,121]
private theorem c397 : Value 1319 rel t397 [1118,273,990,1305,46,121] := .raw [1118,273,990,1305,46,121]
def t398 : Term := .mul t4 t396
private theorem c398 : Value 1319 rel t398 [1143,1302,593,433,1258,818,246,779,874,1066] :=
  .mul [409,63,296,1188] c4 c396 (of_decide_eq_true rfl)
def t399 : Term := .add t397 t398
private theorem c399 : Value 1319 rel t399 [942,256,264,419,1304,939,246,779,874,1066] :=
  .add c397 c398 (of_decide_eq_true rfl)
def t400 : Term := .raw [592,477,226,83,914,811]
private theorem c400 : Value 1319 rel t400 [592,477,226,83,914,811] := .raw [592,477,226,83,914,811]
def t401 : Term := .mul t4 t399
private theorem c401 : Value 1319 rel t401 [317,1192,73,177,420,187,848,1214,334,683] :=
  .mul [272,708,1144,1294,595,825,817,705,154] c4 c399 (of_decide_eq_true rfl)
def t402 : Term := .add t400 t401
private theorem c402 : Value 1319 rel t402 [909,350,299,260,15,998,848,1214,334,683] :=
  .add c400 c401 (of_decide_eq_true rfl)
def t403 : Term := .raw [840,475,648,718,768,926]
private theorem c403 : Value 1319 rel t403 [840,475,648,718,768,926] := .raw [840,475,648,718,768,926]
def t404 : Term := .mul t4 t402
private theorem c404 : Value 1319 rel t404 [778,304,608,952,103,979,889,894,817,731] :=
  .mul [731,176,977,481,970,694,765,847,1190] c4 c402 (of_decide_eq_true rfl)
def t405 : Term := .add t403 t404
private theorem c405 : Value 1319 rel t405 [299,779,1256,351,871,586,889,894,817,731] :=
  .add c403 c404 (of_decide_eq_true rfl)
def t406 : Term := .mul t2 t395
private theorem c406 : Value 1319 rel t406 [992,1103,1042,94,118,1290,1218,1130,910,768] :=
  .mul [216,440,563,249,33,225,1039,139,16] c2 c395 (of_decide_eq_true rfl)
def t407 : Term := .add t405 t406
private theorem c407 : Value 1319 rel t407 [1291,563,979,445,989,557,788,705,408,180] :=
  .add c405 c406 (of_decide_eq_true rfl)
def t408 : Term := .raw [386,843,221,310,741]
private theorem c408 : Value 1319 rel t408 [386,843,221,310,741] := .raw [386,843,221,310,741]
def t409 : Term := .raw [851,770,340,469,486,741]
private theorem c409 : Value 1319 rel t409 [851,770,340,469,486,741] := .raw [851,770,340,469,486,741]
def t410 : Term := .mul t4 t408
private theorem c410 : Value 1319 rel t410 [1120,526,388,783,690,1024,1154,1230,680,694] :=
  .mul [208,740,1188,1040] c4 c408 (of_decide_eq_true rfl)
def t411 : Term := .add t409 t410
private theorem c411 : Value 1319 rel t411 [652,1296,728,1252,1176,446,1154,1230,680,694] :=
  .add c409 c410 (of_decide_eq_true rfl)
def t412 : Term := .raw [1023,963,56,907,830,1206]
private theorem c412 : Value 1319 rel t412 [1023,963,56,907,830,1206] := .raw [1023,963,56,907,830,1206]
def t413 : Term := .mul t4 t411
private theorem c413 : Value 1319 rel t413 [640,933,738,641,1295,368,792,1288,456,199] :=
  .mul [593,752,1033,263,863,185,426,812,1298] c4 c411 (of_decide_eq_true rfl)
def t414 : Term := .add t412 t413
private theorem c414 : Value 1319 rel t414 [344,577,794,229,806,255,792,1288,456,199] :=
  .add c412 c413 (of_decide_eq_true rfl)
def t415 : Term := .raw [664,1135,747,437,496,1027]
private theorem c415 : Value 1319 rel t415 [664,1135,747,437,496,1027] := .raw [664,1135,747,437,496,1027]
def t416 : Term := .mul t4 t414
private theorem c416 : Value 1319 rel t416 [629,163,253,103,197,1211,822,1220,762,932] :=
  .mul [1009,209,669,596,369,533,537,1132,395] c4 c414 (of_decide_eq_true rfl)
def t417 : Term := .add t415 t416
private theorem c417 : Value 1319 rel t417 [1293,1298,1000,540,693,919,822,1220,762,932] :=
  .add c415 c416 (of_decide_eq_true rfl)
def t418 : Term := .mul t2 t407
private theorem c418 : Value 1319 rel t418 [807,711,782,395,64,403,262,969,1311,1169] :=
  .mul [1106,643,587,150,400,475,67,517,127] c2 c407 (of_decide_eq_true rfl)
def t419 : Term := .add t417 t418
private theorem c419 : Value 1319 rel t419 [781,690,463,935,757,3,1084,870,754,782] :=
  .add c417 c418 (of_decide_eq_true rfl)
def t420 : Term := .raw [1167,964,935,256,1283,1168,942,845,1045,983]
private theorem c420 : Value 1319 rel t420 [1167,964,935,256,1283,1168,942,845,1045,983] := .raw [1167,964,935,256,1283,1168,942,845,1045,983]
def t421 : Term := .mul t419 t420
private theorem c421 : Value 1319 rel t421 [1] :=
  .mul [35,1215,460,1157,50,202,828,1237,1048] c419 c420 (of_decide_eq_true rfl)
def t422 : Term := .raw [1116]
private theorem c422 : Value 1319 rel t422 [1116] := .raw [1116]
def t423 : Term := .raw [964,1116]
private theorem c423 : Value 1319 rel t423 [964,1116] := .raw [964,1116]
def t424 : Term := .mul t4 t422
private theorem c424 : Value 1319 rel t424 [1051,358,1128,649,382,1106,774,1019,395,525] :=
  .mul [] c4 c422 (of_decide_eq_true rfl)
def t425 : Term := .add t423 t424
private theorem c425 : Value 1319 rel t425 [696,155,1128,649,382,1106,774,1019,395,525] :=
  .add c423 c424 (of_decide_eq_true rfl)
def t426 : Term := .raw [251,203]
private theorem c426 : Value 1319 rel t426 [251,203] := .raw [251,203]
def t427 : Term := .mul t4 t425
private theorem c427 : Value 1319 rel t427 [1048,1292,575,696,740,1051,441,233,472,961] :=
  .mul [1067,327,140,1025,444,1186,1233,425,598] c4 c425 (of_decide_eq_true rfl)
def t428 : Term := .add t426 t427
private theorem c428 : Value 1319 rel t428 [1299,176,575,696,740,1051,441,233,472,961] :=
  .add c426 c427 (of_decide_eq_true rfl)
def t429 : Term := .raw [813,970]
private theorem c429 : Value 1319 rel t429 [813,970] := .raw [813,970]
def t430 : Term := .mul t4 t428
private theorem c430 : Value 1319 rel t430 [1198,442,649,835,1099,959,518,598,431,599] :=
  .mul [1216,435,742,864,677,655,283,1046,562] c4 c428 (of_decide_eq_true rfl)
def t431 : Term := .add t429 t430
private theorem c431 : Value 1319 rel t431 [692,93,649,835,1099,959,518,598,431,599] :=
  .add c429 c430 (of_decide_eq_true rfl)
def t432 : Term := .raw [440,1116]
private theorem c432 : Value 1319 rel t432 [440,1116] := .raw [440,1116]
def t433 : Term := .raw [387,85,1116]
private theorem c433 : Value 1319 rel t433 [387,85,1116] := .raw [387,85,1116]
def t434 : Term := .mul t4 t432
private theorem c434 : Value 1319 rel t434 [327,729,790,673,381,864,721,765,42,683] :=
  .mul [525] c4 c432 (of_decide_eq_true rfl)
def t435 : Term := .add t433 t434
private theorem c435 : Value 1319 rel t435 [714,814,587,673,381,864,721,765,42,683] :=
  .add c433 c434 (of_decide_eq_true rfl)
def t436 : Term := .raw [910,938,203]
private theorem c436 : Value 1319 rel t436 [910,938,203] := .raw [910,938,203]
def t437 : Term := .mul t4 t435
private theorem c437 : Value 1319 rel t437 [1015,1014,1192,993,1211,143,215,721,624,820] :=
  .mul [1087,212,1076,318,1226,1273,1074,738,1190] c4 c435 (of_decide_eq_true rfl)
def t438 : Term := .add t436 t437
private theorem c438 : Value 1319 rel t438 [606,633,76,993,1211,143,215,721,624,820] :=
  .add c436 c437 (of_decide_eq_true rfl)
def t439 : Term := .raw [1239,1151,970]
private theorem c439 : Value 1319 rel t439 [1239,1151,970] := .raw [1239,1151,970]
def t440 : Term := .mul t4 t438
private theorem c440 : Value 1319 rel t440 [1156,35,925,564,12,726,458,560,190,1198] :=
  .mul [302,1243,1060,807,247,46,894,1304,17] c4 c438 (of_decide_eq_true rfl)
def t441 : Term := .add t439 t440
private theorem c441 : Value 1319 rel t441 [1076,1186,576,564,12,726,458,560,190,1198] :=
  .add c439 c440 (of_decide_eq_true rfl)
def t442 : Term := .mul t5 t431
private theorem c442 : Value 1319 rel t442 [362,460,996,675,736,736,244,166,457,219] :=
  .mul [1131,358,668,984,40,699,200,385,211] c5 c431 (of_decide_eq_true rfl)
def t443 : Term := .add t441 t442
private theorem c443 : Value 1319 rel t443 [119,327,253,1239,748,143,702,726,647,98] :=
  .add c441 c442 (of_decide_eq_true rfl)
def t444 : Term := .raw [742,1177]
private theorem c444 : Value 1319 rel t444 [742,1177] := .raw [742,1177]
def t445 : Term := .raw [56,827,1177]
private theorem c445 : Value 1319 rel t445 [56,827,1177] := .raw [56,827,1177]
def t446 : Term := .mul t4 t444
private theorem c446 : Value 1319 rel t446 [1180,880,557,3,875,159,1048,235,424,618] :=
  .mul [1004] c4 c444 (of_decide_eq_true rfl)
def t447 : Term := .add t445 t446
private theorem c447 : Value 1319 rel t447 [1236,388,415,3,875,159,1048,235,424,618] :=
  .add c445 c446 (of_decide_eq_true rfl)
def t448 : Term := .raw [581,884,14]
private theorem c448 : Value 1319 rel t448 [581,884,14] := .raw [581,884,14]
def t449 : Term := .mul t4 t447
private theorem c449 : Value 1319 rel t449 [280,262,47,350,925,844,1136,1129,536,715] :=
  .mul [300,620,1053,120,717,432,1067,1256,312] c4 c447 (of_decide_eq_true rfl)
def t450 : Term := .add t448 t449
private theorem c450 : Value 1319 rel t450 [861,1146,61,350,925,844,1136,1129,536,715] :=
  .add c448 c449 (of_decide_eq_true rfl)
def t451 : Term := .raw [1076,502,801]
private theorem c451 : Value 1319 rel t451 [1076,502,801] := .raw [1076,502,801]
def t452 : Term := .mul t4 t450
private theorem c452 : Value 1319 rel t452 [658,1242,771,753,1316,351,104,750,639,378] :=
  .mul [889,352,1066,1056,92,1138,783,651,425] c4 c450 (of_decide_eq_true rfl)
def t453 : Term := .add t451 t452
private theorem c453 : Value 1319 rel t453 [415,425,253,753,1316,351,104,750,639,378] :=
  .add c451 c452 (of_decide_eq_true rfl)
def t454 : Term := .mul t5 t443
private theorem c454 : Value 1319 rel t454 [1235,390,515,84,519,787,684,918,398,193] :=
  .mul [982,477,210,221,7,412,730,13,781] c5 c443 (of_decide_eq_true rfl)
def t455 : Term := .add t453 t454
private theorem c455 : Value 1319 rel t455 [331,815,768,837,516,1138,788,349,1037,571] :=
  .add c453 c454 (of_decide_eq_true rfl)
def t456 : Term := .raw [114]
private theorem c456 : Value 1319 rel t456 [114] := .raw [114]
def t457 : Term := .raw [1052,114]
private theorem c457 : Value 1319 rel t457 [1052,114] := .raw [1052,114]
def t458 : Term := .mul t4 t456
private theorem c458 : Value 1319 rel t458 [157,1001,796,1052,1046,425,462,97,246,160] :=
  .mul [] c4 c456 (of_decide_eq_true rfl)
def t459 : Term := .add t457 t458
private theorem c459 : Value 1319 rel t459 [1209,1115,796,1052,1046,425,462,97,246,160] :=
  .add c457 c458 (of_decide_eq_true rfl)
def t460 : Term := .raw [1086,1109]
private theorem c460 : Value 1319 rel t460 [1086,1109] := .raw [1086,1109]
def t461 : Term := .mul t4 t459
private theorem c461 : Value 1319 rel t461 [1208,87,295,72,1305,771,1106,468,539,1294] :=
  .mul [187,778,922,438,173,575,828,632,132] c4 c459 (of_decide_eq_true rfl)
def t462 : Term := .add t460 t461
private theorem c462 : Value 1319 rel t462 [975,1196,295,72,1305,771,1106,468,539,1294] :=
  .add c460 c461 (of_decide_eq_true rfl)
def t463 : Term := .raw [1114,841]
private theorem c463 : Value 1319 rel t463 [1114,841] := .raw [1114,841]
def t464 : Term := .mul t4 t462
private theorem c464 : Value 1319 rel t464 [169,485,433,417,514,1128,146,1072,785,1057] :=
  .mul [387,846,1014,71,577,284,866,1134,474] c4 c462 (of_decide_eq_true rfl)
def t465 : Term := .add t463 t464
private theorem c465 : Value 1319 rel t465 [1283,7,433,417,514,1128,146,1072,785,1057] :=
  .add c463 c464 (of_decide_eq_true rfl)
def t466 : Term := .raw [887,114]
private theorem c466 : Value 1319 rel t466 [887,114] := .raw [887,114]
def t467 : Term := .raw [626,620,114]
private theorem c467 : Value 1319 rel t467 [626,620,114] := .raw [626,620,114]
def t468 : Term := .mul t4 t466
private theorem c468 : Value 1319 rel t468 [470,196,115,327,644,509,1230,1033,577,1035] :=
  .mul [160] c4 c466 (of_decide_eq_true rfl)
def t469 : Term := .add t467 t468
private theorem c469 : Value 1319 rel t469 [1096,816,229,327,644,509,1230,1033,577,1035] :=
  .add c467 c468 (of_decide_eq_true rfl)
def t470 : Term := .raw [1178,1255,1109]
private theorem c470 : Value 1319 rel t470 [1178,1255,1109] := .raw [1178,1255,1109]
def t471 : Term := .mul t4 t469
private theorem c471 : Value 1319 rel t471 [984,1190,454,273,750,973,1169,304,1185,143] :=
  .mul [527,1295,633,470,235,1262,1093,125,689] c4 c469 (of_decide_eq_true rfl)
def t472 : Term := .add t470 t471
private theorem c472 : Value 1319 rel t472 [843,1126,244,273,750,973,1169,304,1185,143] :=
  .add c470 c471 (of_decide_eq_true rfl)
def t473 : Term := .raw [511,1108,841]
private theorem c473 : Value 1319 rel t473 [511,1108,841] := .raw [511,1108,841]
def t474 : Term := .mul t4 t472
private theorem c474 : Value 1319 rel t474 [466,527,378,799,732,179,1194,792,512,1074] :=
  .mul [882,154,430,1084,941,1216,1061,472,85] c4 c472 (of_decide_eq_true rfl)
def t475 : Term := .add t473 t474
private theorem c475 : Value 1319 rel t475 [977,316,1219,799,732,179,1194,792,512,1074] :=
  .add c473 c474 (of_decide_eq_true rfl)
def t476 : Term := .mul t5 t465
private theorem c476 : Value 1319 rel t476 [894,471,538,12,683,474,606,1019,1004,368] :=
  .mul [16,745,406,690,1003,308,944,1277,227] c5 c465 (of_decide_eq_true rfl)
def t477 : Term := .add t475 t476
private theorem c477 : Value 1319 rel t477 [552,787,438,811,96,653,481,492,197,123] :=
  .add c475 c476 (of_decide_eq_true rfl)
def t478 : Term := .raw [234,149]
private theorem c478 : Value 1319 rel t478 [234,149] := .raw [234,149]
def t479 : Term := .raw [432,1074,149]
private theorem c479 : Value 1319 rel t479 [432,1074,149] := .raw [432,1074,149]
def t480 : Term := .mul t4 t478
private theorem c480 : Value 1319 rel t480 [3,1223,198,276,1186,1166,847,732,471,349] :=
  .mul [24] c4 c478 (of_decide_eq_true rfl)
def t481 : Term := .add t479 t480
private theorem c481 : Value 1319 rel t481 [435,978,347,276,1186,1166,847,732,471,349] :=
  .add c479 c480 (of_decide_eq_true rfl)
def t482 : Term := .raw [550,868,255]
private theorem c482 : Value 1319 rel t482 [550,868,255] := .raw [550,868,255]
def t483 : Term := .mul t4 t481
private theorem c483 : Value 1319 rel t483 [998,1053,1003,754,741,4,345,495,50,339] :=
  .mul [107,786,960,1281,152,426,977,207,189] c4 c481 (of_decide_eq_true rfl)
def t484 : Term := .add t482 t483
private theorem c484 : Value 1319 rel t484 [229,602,1258,754,741,4,345,495,50,339] :=
  .add c482 c483 (of_decide_eq_true rfl)
def t485 : Term := .raw [211,37,0]
private theorem c485 : Value 1319 rel t485 [211,37,0] := .raw [211,37,0]
def t486 : Term := .mul t4 t484
private theorem c486 : Value 1319 rel t486 [763,605,1062,1223,24,1009,511,1303,187,539] :=
  .mul [1084,318,304,247,644,1064,196,142,1170] c4 c484 (of_decide_eq_true rfl)
def t487 : Term := .add t485 t486
private theorem c487 : Value 1319 rel t487 [974,642,1062,1223,24,1009,511,1303,187,539] :=
  .add c485 c486 (of_decide_eq_true rfl)
def t488 : Term := .mul t5 t477
private theorem c488 : Value 1319 rel t488 [1310,248,594,892,469,221,675,676,997,978] :=
  .mul [417,342,585,307,762,1117,1070,1113,563] c5 c477 (of_decide_eq_true rfl)
def t489 : Term := .add t487 t488
private theorem c489 : Value 1319 rel t489 [965,890,337,796,493,1230,1186,660,1184,198] :=
  .add c487 c488 (of_decide_eq_true rfl)
def t490 : Term := .mul t2 t455
private theorem c490 : Value 1319 rel t490 [480,63,1092,296,335,146,375,587,1086,66] :=
  .mul [1272,877,1006,268,1013,241,882,800,674] c2 c455 (of_decide_eq_true rfl)
def t491 : Term := .add t489 t490
private theorem c491 : Value 1319 rel t491 [126,953,110,1092,828,57,242,1247,951,264] :=
  .add c489 c490 (of_decide_eq_true rfl)
def t492 : Term := .raw [819,594,182,745,430,659,840,227,894,1105]
private theorem c492 : Value 1319 rel t492 [819,594,182,745,430,659,840,227,894,1105] := .raw [819,594,182,745,430,659,840,227,894,1105]
def t493 : Term := .mul t491 t492
private theorem c493 : Value 1319 rel t493 [1] :=
  .mul [1208,443,504,115,1235,939,996,626,221] c491 c492 (of_decide_eq_true rfl)
def t494 : Term := .mul t3 t374
private theorem c494 : Value 1319 rel t494 [115,214,786,964,649,158,153,284,1042,22] :=
  .mul [1171,445,986,62,98,243,1229,602,966,238,401,145,68] c3 c374 (of_decide_eq_true rfl)
def t495 : Term := .add t375 t494
private theorem c495 : Value 1319 rel t495 [98,638,1169,1303,1117,634,1276,641,1201,401,1112,220,137,1154,891] :=
  .add c375 c494 (of_decide_eq_true rfl)
def t496 : Term := .mul t3 t495
private theorem c496 : Value 1319 rel t496 [678,711,1074,73,298,1002,1129,276,268,432] :=
  .mul [433,264,582,1301,45,52,585,741,762,341,1082,249,748,68] c3 c495 (of_decide_eq_true rfl)
def t497 : Term := .add t378 t496
private theorem c497 : Value 1319 rel t497 [547,317,1252,1094,877,301,165,1043,852,1147,1239,440,564,353,258] :=
  .add c378 c496 (of_decide_eq_true rfl)
def t498 : Term := .mul t3 t497
private theorem c498 : Value 1319 rel t498 [1102,1114,643,432,1014,1233,1248,205,972,808] :=
  .mul [899,34,602,293,400,389,1231,881,288,1019,441,74,625,637] c3 c497 (of_decide_eq_true rfl)
def t499 : Term := .add t381 t498
private theorem c499 : Value 1319 rel t499 [1051,133,524,674,1147,1117,917,115,401,882,539,433,8,59,90] :=
  .add c381 c498 (of_decide_eq_true rfl)
def t500 : Term := .raw [828,424,1226,31,938,710,136,1268,314,301]
private theorem c500 : Value 1319 rel t500 [828,424,1226,31,938,710,136,1268,314,301] := .raw [828,424,1226,31,938,710,136,1268,314,301]
def t501 : Term := .mul t499 t500
private theorem c501 : Value 1319 rel t501 [1] :=
  .mul [574,263,891,336,225,1300,108,463,1231,86,1075,1049,1260,710] c499 c500 (of_decide_eq_true rfl)
def t502 : Term := .mul t3 t395
private theorem c502 : Value 1319 rel t502 [116,996,1023,478,299,1174,699,234,197,69] :=
  .mul [734,1210,1245,50,852,1158,207,123,512] c3 c395 (of_decide_eq_true rfl)
def t503 : Term := .add t405 t502
private theorem c503 : Value 1319 rel t503 [415,456,960,829,1170,441,269,1128,1014,800] :=
  .add c405 c502 (of_decide_eq_true rfl)
def t504 : Term := .mul t3 t503
private theorem c504 : Value 1319 rel t504 [254,17,164,360,1288,384,1032,1007,1235,674] :=
  .mul [987,722,1167,694,122,318,346,653,329] c3 c503 (of_decide_eq_true rfl)
def t505 : Term := .add t417 t504
private theorem c505 : Value 1319 rel t505 [228,1315,1164,900,662,1303,535,908,678,287] :=
  .add c417 c504 (of_decide_eq_true rfl)
def t506 : Term := .raw [856,1055,449,869,1231,795,846,1170,41,935]
private theorem c506 : Value 1319 rel t506 [856,1055,449,869,1231,795,846,1170,41,935] := .raw [856,1055,449,869,1231,795,846,1170,41,935]
def t507 : Term := .mul t505 t506
private theorem c507 : Value 1319 rel t507 [1] :=
  .mul [525,1222,40,915,986,828,234,622,588] c505 c506 (of_decide_eq_true rfl)
def t508 : Term := .mul t5 t374
private theorem c508 : Value 1319 rel t508 [632,413,162,131,91,1164,63,97,1175,346] :=
  .mul [38,533,892,1105,120,918,1076,86,762,854,1259,1036,250] c5 c374 (of_decide_eq_true rfl)
def t509 : Term := .add t375 t508
private theorem c509 : Value 1319 rel t509 [615,837,545,470,559,321,1186,454,15,725,1112,220,137,1154,891] :=
  .add c375 c508 (of_decide_eq_true rfl)
def t510 : Term := .mul t5 t509
private theorem c510 : Value 1319 rel t510 [670,144,803,1252,609,53,1026,823,401,963] :=
  .mul [403,920,689,224,814,196,327,196,1131,770,739,213,33,250] c5 c509 (of_decide_eq_true rfl)
def t511 : Term := .add t378 t510
private theorem c511 : Value 1319 rel t511 [539,1069,981,954,1188,671,62,271,985,359,1239,440,564,353,258] :=
  .add c378 c510 (of_decide_eq_true rfl)
def t512 : Term := .mul t5 t511
private theorem c512 : Value 1319 rel t512 [1161,1150,1020,840,1065,671,1079,675,29,394] :=
  .mul [707,126,579,1118,11,135,143,885,485,605,523,890,1228,441] c5 c511 (of_decide_eq_true rfl)
def t513 : Term := .add t381 t512
private theorem c513 : Value 1319 rel t513 [1110,169,901,1082,1198,555,748,585,777,468,539,433,8,59,90] :=
  .add c381 c512 (of_decide_eq_true rfl)
def t514 : Term := .raw [1316,489,907,953,611,460,717,1248,234,254]
private theorem c514 : Value 1319 rel t514 [1316,489,907,953,611,460,717,1248,234,254] := .raw [1316,489,907,953,611,460,717,1248,234,254]
def t515 : Term := .mul t513 t514
private theorem c515 : Value 1319 rel t515 [1] :=
  .mul [171,597,1049,473,720,68,1208,1008,1243,294,216,544,559,437] c513 c514 (of_decide_eq_true rfl)

def terminalExpression : Term := t373
theorem terminalProof : Value 1319 rel terminalExpression [1] := c373
def h0Expression : Term := t385
theorem h0Proof : Value 1319 rel h0Expression [1] := c385
def u0Expression : Term := t421
theorem u0Proof : Value 1319 rel u0Expression [1] := c421
def v0Expression : Term := t493
theorem v0Proof : Value 1319 rel v0Expression [1] := c493
def h1Expression : Term := t501
theorem h1Proof : Value 1319 rel h1Expression [1] := c501
def u1Expression : Term := t507
theorem u1Proof : Value 1319 rel u1Expression [1] := c507
def h3Expression : Term := t515
theorem h3Proof : Value 1319 rel h3Expression [1] := c515
def pencilExpression : List Term := [t13,t19,t25,t27,t1]
def splitExpression : List Term := [t38,t41,t42,t43,t1]
theorem splitProof : SameValues 1319 rel pencilExpression splitExpression :=
  .cons c13 c38 (.cons c19 c41 (.cons c25 c42 (.cons c27 c43 (.cons c1 c1 (.nil)))))

end RKCert.CompactResidue.Tape7
