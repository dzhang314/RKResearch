module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorLiteralStripRows

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

def slice080Packets : List StripRowPacket :=
  [packet1035, packet1038, packet1039, packet1047, packet1048, packet1051,
   packet1052, packet1141, packet1143, packet1144, packet1155, packet1156,
   packet1159, packet1160, packet1195, packet1197, packet1200, packet1201]

def slice080 : GridSlice := closedSliceOfPackets 232 236 slice080Packets

private theorem slice080_checked_local : checkSlice slice080.vertical 64 slice080 = true := by
  decide +kernel

theorem slice080_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice080 = true := by
  apply sliceCheck_of_packets slice080_checked_local
  intro p hp
  simp only [slice080Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets043_group packet1035_membership
  · exact packet_mem_of_chunk packets043_group packet1038_membership
  · exact packet_mem_of_chunk packets043_group packet1039_membership
  · exact packet_mem_of_chunk packets043_group packet1047_membership
  · exact packet_mem_of_chunk packets043_group packet1048_membership
  · exact packet_mem_of_chunk packets043_group packet1051_membership
  · exact packet_mem_of_chunk packets043_group packet1052_membership
  · exact packet_mem_of_chunk packets047_group packet1141_membership
  · exact packet_mem_of_chunk packets047_group packet1143_membership
  · exact packet_mem_of_chunk packets047_group packet1144_membership
  · exact packet_mem_of_chunk packets048_group packet1155_membership
  · exact packet_mem_of_chunk packets048_group packet1156_membership
  · exact packet_mem_of_chunk packets048_group packet1159_membership
  · exact packet_mem_of_chunk packets048_group packet1160_membership
  · exact packet_mem_of_chunk packets049_group packet1195_membership
  · exact packet_mem_of_chunk packets049_group packet1197_membership
  · exact packet_mem_of_chunk packets050_group packet1200_membership
  · exact packet_mem_of_chunk packets050_group packet1201_membership

def slice081Packets : List StripRowPacket :=
  [packet1035, packet1038, packet1039, packet1047, packet1048, packet1051,
   packet1052, packet1142, packet1145, packet1146, packet1157, packet1158,
   packet1161, packet1162, packet1196, packet1197, packet1200, packet1201]

def slice081 : GridSlice := closedSliceOfPackets 236 240 slice081Packets

private theorem slice081_checked_local : checkSlice slice081.vertical 64 slice081 = true := by
  decide +kernel

theorem slice081_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice081 = true := by
  apply sliceCheck_of_packets slice081_checked_local
  intro p hp
  simp only [slice081Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets043_group packet1035_membership
  · exact packet_mem_of_chunk packets043_group packet1038_membership
  · exact packet_mem_of_chunk packets043_group packet1039_membership
  · exact packet_mem_of_chunk packets043_group packet1047_membership
  · exact packet_mem_of_chunk packets043_group packet1048_membership
  · exact packet_mem_of_chunk packets043_group packet1051_membership
  · exact packet_mem_of_chunk packets043_group packet1052_membership
  · exact packet_mem_of_chunk packets047_group packet1142_membership
  · exact packet_mem_of_chunk packets047_group packet1145_membership
  · exact packet_mem_of_chunk packets047_group packet1146_membership
  · exact packet_mem_of_chunk packets048_group packet1157_membership
  · exact packet_mem_of_chunk packets048_group packet1158_membership
  · exact packet_mem_of_chunk packets048_group packet1161_membership
  · exact packet_mem_of_chunk packets048_group packet1162_membership
  · exact packet_mem_of_chunk packets049_group packet1196_membership
  · exact packet_mem_of_chunk packets049_group packet1197_membership
  · exact packet_mem_of_chunk packets050_group packet1200_membership
  · exact packet_mem_of_chunk packets050_group packet1201_membership

def slice082Packets : List StripRowPacket :=
  [packet1040, packet1041, packet1042, packet1053, packet1054, packet1057,
   packet1058, packet1163, packet1165, packet1166, packet1176, packet1177,
   packet1180, packet1181, packet1202, packet1204, packet1208, packet1209]

def slice082 : GridSlice := closedSliceOfPackets 240 244 slice082Packets

private theorem slice082_checked_local : checkSlice slice082.vertical 64 slice082 = true := by
  decide +kernel

theorem slice082_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice082 = true := by
  apply sliceCheck_of_packets slice082_checked_local
  intro p hp
  simp only [slice082Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets043_group packet1040_membership
  · exact packet_mem_of_chunk packets043_group packet1041_membership
  · exact packet_mem_of_chunk packets043_group packet1042_membership
  · exact packet_mem_of_chunk packets043_group packet1053_membership
  · exact packet_mem_of_chunk packets043_group packet1054_membership
  · exact packet_mem_of_chunk packets044_group packet1057_membership
  · exact packet_mem_of_chunk packets044_group packet1058_membership
  · exact packet_mem_of_chunk packets048_group packet1163_membership
  · exact packet_mem_of_chunk packets048_group packet1165_membership
  · exact packet_mem_of_chunk packets048_group packet1166_membership
  · exact packet_mem_of_chunk packets049_group packet1176_membership
  · exact packet_mem_of_chunk packets049_group packet1177_membership
  · exact packet_mem_of_chunk packets049_group packet1180_membership
  · exact packet_mem_of_chunk packets049_group packet1181_membership
  · exact packet_mem_of_chunk packets050_group packet1202_membership
  · exact packet_mem_of_chunk packets050_group packet1204_membership
  · exact packet_mem_of_chunk packets050_group packet1208_membership
  · exact packet_mem_of_chunk packets050_group packet1209_membership

def slice083Packets : List StripRowPacket :=
  [packet1040, packet1041, packet1042, packet1053, packet1054, packet1057,
   packet1058, packet1164, packet1167, packet1168, packet1178, packet1179,
   packet1182, packet1183, packet1203, packet1204, packet1208, packet1209]

def slice083 : GridSlice := closedSliceOfPackets 244 248 slice083Packets

private theorem slice083_checked_local : checkSlice slice083.vertical 64 slice083 = true := by
  decide +kernel

theorem slice083_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice083 = true := by
  apply sliceCheck_of_packets slice083_checked_local
  intro p hp
  simp only [slice083Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets043_group packet1040_membership
  · exact packet_mem_of_chunk packets043_group packet1041_membership
  · exact packet_mem_of_chunk packets043_group packet1042_membership
  · exact packet_mem_of_chunk packets043_group packet1053_membership
  · exact packet_mem_of_chunk packets043_group packet1054_membership
  · exact packet_mem_of_chunk packets044_group packet1057_membership
  · exact packet_mem_of_chunk packets044_group packet1058_membership
  · exact packet_mem_of_chunk packets048_group packet1164_membership
  · exact packet_mem_of_chunk packets048_group packet1167_membership
  · exact packet_mem_of_chunk packets048_group packet1168_membership
  · exact packet_mem_of_chunk packets049_group packet1178_membership
  · exact packet_mem_of_chunk packets049_group packet1179_membership
  · exact packet_mem_of_chunk packets049_group packet1182_membership
  · exact packet_mem_of_chunk packets049_group packet1183_membership
  · exact packet_mem_of_chunk packets050_group packet1203_membership
  · exact packet_mem_of_chunk packets050_group packet1204_membership
  · exact packet_mem_of_chunk packets050_group packet1208_membership
  · exact packet_mem_of_chunk packets050_group packet1209_membership

def slice084Packets : List StripRowPacket :=
  [packet1040, packet1043, packet1044, packet1055, packet1056, packet1059,
   packet1060, packet1169, packet1172, packet1173, packet1184, packet1185,
   packet1188, packet1189, packet1205, packet1207, packet1210, packet1211]

def slice084 : GridSlice := closedSliceOfPackets 248 252 slice084Packets

private theorem slice084_checked_local : checkSlice slice084.vertical 64 slice084 = true := by
  decide +kernel

theorem slice084_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice084 = true := by
  apply sliceCheck_of_packets slice084_checked_local
  intro p hp
  simp only [slice084Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets043_group packet1040_membership
  · exact packet_mem_of_chunk packets043_group packet1043_membership
  · exact packet_mem_of_chunk packets043_group packet1044_membership
  · exact packet_mem_of_chunk packets043_group packet1055_membership
  · exact packet_mem_of_chunk packets044_group packet1056_membership
  · exact packet_mem_of_chunk packets044_group packet1059_membership
  · exact packet_mem_of_chunk packets044_group packet1060_membership
  · exact packet_mem_of_chunk packets048_group packet1169_membership
  · exact packet_mem_of_chunk packets048_group packet1172_membership
  · exact packet_mem_of_chunk packets048_group packet1173_membership
  · exact packet_mem_of_chunk packets049_group packet1184_membership
  · exact packet_mem_of_chunk packets049_group packet1185_membership
  · exact packet_mem_of_chunk packets049_group packet1188_membership
  · exact packet_mem_of_chunk packets049_group packet1189_membership
  · exact packet_mem_of_chunk packets050_group packet1205_membership
  · exact packet_mem_of_chunk packets050_group packet1207_membership
  · exact packet_mem_of_chunk packets050_group packet1210_membership
  · exact packet_mem_of_chunk packets050_group packet1211_membership

def slice085Packets : List StripRowPacket :=
  [packet1040, packet1043, packet1044, packet1055, packet1056, packet1059,
   packet1060, packet1170, packet1171, packet1174, packet1175, packet1186,
   packet1187, packet1190, packet1191, packet1206, packet1207, packet1210,
   packet1211]

def slice085 : GridSlice := closedSliceOfPackets 252 256 slice085Packets

private theorem slice085_checked_local : checkSlice slice085.vertical 64 slice085 = true := by
  decide +kernel

theorem slice085_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice085 = true := by
  apply sliceCheck_of_packets slice085_checked_local
  intro p hp
  simp only [slice085Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets043_group packet1040_membership
  · exact packet_mem_of_chunk packets043_group packet1043_membership
  · exact packet_mem_of_chunk packets043_group packet1044_membership
  · exact packet_mem_of_chunk packets043_group packet1055_membership
  · exact packet_mem_of_chunk packets044_group packet1056_membership
  · exact packet_mem_of_chunk packets044_group packet1059_membership
  · exact packet_mem_of_chunk packets044_group packet1060_membership
  · exact packet_mem_of_chunk packets048_group packet1170_membership
  · exact packet_mem_of_chunk packets048_group packet1171_membership
  · exact packet_mem_of_chunk packets048_group packet1174_membership
  · exact packet_mem_of_chunk packets048_group packet1175_membership
  · exact packet_mem_of_chunk packets049_group packet1186_membership
  · exact packet_mem_of_chunk packets049_group packet1187_membership
  · exact packet_mem_of_chunk packets049_group packet1190_membership
  · exact packet_mem_of_chunk packets049_group packet1191_membership
  · exact packet_mem_of_chunk packets050_group packet1206_membership
  · exact packet_mem_of_chunk packets050_group packet1207_membership
  · exact packet_mem_of_chunk packets050_group packet1210_membership
  · exact packet_mem_of_chunk packets050_group packet1211_membership


end RKCert.ReviewedNative.ThreeInteriorPencil
