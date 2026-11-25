module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorLiteralStripRows

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

def slice072Packets : List StripRowPacket :=
  [packet1010, packet1012, packet1013, packet1021, packet1022, packet1025,
   packet1026, packet1067, packet1069, packet1070, packet1079, packet1080,
   packet1083, packet1084, packet1118, packet1120, packet1123, packet1124]

def slice072 : GridSlice := closedSliceOfPackets 200 204 slice072Packets

private theorem slice072_checked_local : checkSlice slice072.vertical 64 slice072 = true := by
  decide +kernel

theorem slice072_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice072 = true := by
  apply sliceCheck_of_packets slice072_checked_local
  intro p hp
  simp only [slice072Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets042_group packet1010_membership
  · exact packet_mem_of_chunk packets042_group packet1012_membership
  · exact packet_mem_of_chunk packets042_group packet1013_membership
  · exact packet_mem_of_chunk packets042_group packet1021_membership
  · exact packet_mem_of_chunk packets042_group packet1022_membership
  · exact packet_mem_of_chunk packets042_group packet1025_membership
  · exact packet_mem_of_chunk packets042_group packet1026_membership
  · exact packet_mem_of_chunk packets044_group packet1067_membership
  · exact packet_mem_of_chunk packets044_group packet1069_membership
  · exact packet_mem_of_chunk packets044_group packet1070_membership
  · exact packet_mem_of_chunk packets044_group packet1079_membership
  · exact packet_mem_of_chunk packets045_group packet1080_membership
  · exact packet_mem_of_chunk packets045_group packet1083_membership
  · exact packet_mem_of_chunk packets045_group packet1084_membership
  · exact packet_mem_of_chunk packets046_group packet1118_membership
  · exact packet_mem_of_chunk packets046_group packet1120_membership
  · exact packet_mem_of_chunk packets046_group packet1123_membership
  · exact packet_mem_of_chunk packets046_group packet1124_membership

def slice073Packets : List StripRowPacket :=
  [packet1010, packet1012, packet1013, packet1021, packet1022, packet1025,
   packet1026, packet1068, packet1071, packet1072, packet1081, packet1082,
   packet1085, packet1086, packet1119, packet1120, packet1123, packet1124]

def slice073 : GridSlice := closedSliceOfPackets 204 208 slice073Packets

private theorem slice073_checked_local : checkSlice slice073.vertical 64 slice073 = true := by
  decide +kernel

theorem slice073_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice073 = true := by
  apply sliceCheck_of_packets slice073_checked_local
  intro p hp
  simp only [slice073Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets042_group packet1010_membership
  · exact packet_mem_of_chunk packets042_group packet1012_membership
  · exact packet_mem_of_chunk packets042_group packet1013_membership
  · exact packet_mem_of_chunk packets042_group packet1021_membership
  · exact packet_mem_of_chunk packets042_group packet1022_membership
  · exact packet_mem_of_chunk packets042_group packet1025_membership
  · exact packet_mem_of_chunk packets042_group packet1026_membership
  · exact packet_mem_of_chunk packets044_group packet1068_membership
  · exact packet_mem_of_chunk packets044_group packet1071_membership
  · exact packet_mem_of_chunk packets044_group packet1072_membership
  · exact packet_mem_of_chunk packets045_group packet1081_membership
  · exact packet_mem_of_chunk packets045_group packet1082_membership
  · exact packet_mem_of_chunk packets045_group packet1085_membership
  · exact packet_mem_of_chunk packets045_group packet1086_membership
  · exact packet_mem_of_chunk packets046_group packet1119_membership
  · exact packet_mem_of_chunk packets046_group packet1120_membership
  · exact packet_mem_of_chunk packets046_group packet1123_membership
  · exact packet_mem_of_chunk packets046_group packet1124_membership

def slice074Packets : List StripRowPacket :=
  [packet1014, packet1015, packet1016, packet1027, packet1028, packet1031,
   packet1032, packet1087, packet1089, packet1090, packet1099, packet1100,
   packet1103, packet1104, packet1125, packet1127, packet1131, packet1132]

def slice074 : GridSlice := closedSliceOfPackets 208 212 slice074Packets

private theorem slice074_checked_local : checkSlice slice074.vertical 64 slice074 = true := by
  decide +kernel

theorem slice074_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice074 = true := by
  apply sliceCheck_of_packets slice074_checked_local
  intro p hp
  simp only [slice074Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets042_group packet1014_membership
  · exact packet_mem_of_chunk packets042_group packet1015_membership
  · exact packet_mem_of_chunk packets042_group packet1016_membership
  · exact packet_mem_of_chunk packets042_group packet1027_membership
  · exact packet_mem_of_chunk packets042_group packet1028_membership
  · exact packet_mem_of_chunk packets042_group packet1031_membership
  · exact packet_mem_of_chunk packets043_group packet1032_membership
  · exact packet_mem_of_chunk packets045_group packet1087_membership
  · exact packet_mem_of_chunk packets045_group packet1089_membership
  · exact packet_mem_of_chunk packets045_group packet1090_membership
  · exact packet_mem_of_chunk packets045_group packet1099_membership
  · exact packet_mem_of_chunk packets045_group packet1100_membership
  · exact packet_mem_of_chunk packets045_group packet1103_membership
  · exact packet_mem_of_chunk packets046_group packet1104_membership
  · exact packet_mem_of_chunk packets046_group packet1125_membership
  · exact packet_mem_of_chunk packets046_group packet1127_membership
  · exact packet_mem_of_chunk packets047_group packet1131_membership
  · exact packet_mem_of_chunk packets047_group packet1132_membership

def slice075Packets : List StripRowPacket :=
  [packet1014, packet1015, packet1016, packet1027, packet1028, packet1031,
   packet1032, packet1088, packet1091, packet1092, packet1101, packet1102,
   packet1105, packet1106, packet1126, packet1127, packet1131, packet1132]

def slice075 : GridSlice := closedSliceOfPackets 212 216 slice075Packets

private theorem slice075_checked_local : checkSlice slice075.vertical 64 slice075 = true := by
  decide +kernel

theorem slice075_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice075 = true := by
  apply sliceCheck_of_packets slice075_checked_local
  intro p hp
  simp only [slice075Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets042_group packet1014_membership
  · exact packet_mem_of_chunk packets042_group packet1015_membership
  · exact packet_mem_of_chunk packets042_group packet1016_membership
  · exact packet_mem_of_chunk packets042_group packet1027_membership
  · exact packet_mem_of_chunk packets042_group packet1028_membership
  · exact packet_mem_of_chunk packets042_group packet1031_membership
  · exact packet_mem_of_chunk packets043_group packet1032_membership
  · exact packet_mem_of_chunk packets045_group packet1088_membership
  · exact packet_mem_of_chunk packets045_group packet1091_membership
  · exact packet_mem_of_chunk packets045_group packet1092_membership
  · exact packet_mem_of_chunk packets045_group packet1101_membership
  · exact packet_mem_of_chunk packets045_group packet1102_membership
  · exact packet_mem_of_chunk packets046_group packet1105_membership
  · exact packet_mem_of_chunk packets046_group packet1106_membership
  · exact packet_mem_of_chunk packets046_group packet1126_membership
  · exact packet_mem_of_chunk packets046_group packet1127_membership
  · exact packet_mem_of_chunk packets047_group packet1131_membership
  · exact packet_mem_of_chunk packets047_group packet1132_membership

def slice076Packets : List StripRowPacket :=
  [packet1014, packet1017, packet1018, packet1029, packet1030, packet1033,
   packet1034, packet1093, packet1095, packet1096, packet1107, packet1108,
   packet1111, packet1112, packet1128, packet1130, packet1133, packet1134]

def slice076 : GridSlice := closedSliceOfPackets 216 220 slice076Packets

private theorem slice076_checked_local : checkSlice slice076.vertical 64 slice076 = true := by
  decide +kernel

theorem slice076_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice076 = true := by
  apply sliceCheck_of_packets slice076_checked_local
  intro p hp
  simp only [slice076Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets042_group packet1014_membership
  · exact packet_mem_of_chunk packets042_group packet1017_membership
  · exact packet_mem_of_chunk packets042_group packet1018_membership
  · exact packet_mem_of_chunk packets042_group packet1029_membership
  · exact packet_mem_of_chunk packets042_group packet1030_membership
  · exact packet_mem_of_chunk packets043_group packet1033_membership
  · exact packet_mem_of_chunk packets043_group packet1034_membership
  · exact packet_mem_of_chunk packets045_group packet1093_membership
  · exact packet_mem_of_chunk packets045_group packet1095_membership
  · exact packet_mem_of_chunk packets045_group packet1096_membership
  · exact packet_mem_of_chunk packets046_group packet1107_membership
  · exact packet_mem_of_chunk packets046_group packet1108_membership
  · exact packet_mem_of_chunk packets046_group packet1111_membership
  · exact packet_mem_of_chunk packets046_group packet1112_membership
  · exact packet_mem_of_chunk packets047_group packet1128_membership
  · exact packet_mem_of_chunk packets047_group packet1130_membership
  · exact packet_mem_of_chunk packets047_group packet1133_membership
  · exact packet_mem_of_chunk packets047_group packet1134_membership

def slice077Packets : List StripRowPacket :=
  [packet1014, packet1017, packet1018, packet1029, packet1030, packet1033,
   packet1034, packet1094, packet1097, packet1098, packet1109, packet1110,
   packet1113, packet1114, packet1129, packet1130, packet1133, packet1134]

def slice077 : GridSlice := closedSliceOfPackets 220 224 slice077Packets

private theorem slice077_checked_local : checkSlice slice077.vertical 64 slice077 = true := by
  decide +kernel

theorem slice077_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice077 = true := by
  apply sliceCheck_of_packets slice077_checked_local
  intro p hp
  simp only [slice077Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets042_group packet1014_membership
  · exact packet_mem_of_chunk packets042_group packet1017_membership
  · exact packet_mem_of_chunk packets042_group packet1018_membership
  · exact packet_mem_of_chunk packets042_group packet1029_membership
  · exact packet_mem_of_chunk packets042_group packet1030_membership
  · exact packet_mem_of_chunk packets043_group packet1033_membership
  · exact packet_mem_of_chunk packets043_group packet1034_membership
  · exact packet_mem_of_chunk packets045_group packet1094_membership
  · exact packet_mem_of_chunk packets045_group packet1097_membership
  · exact packet_mem_of_chunk packets045_group packet1098_membership
  · exact packet_mem_of_chunk packets046_group packet1109_membership
  · exact packet_mem_of_chunk packets046_group packet1110_membership
  · exact packet_mem_of_chunk packets046_group packet1113_membership
  · exact packet_mem_of_chunk packets046_group packet1114_membership
  · exact packet_mem_of_chunk packets047_group packet1129_membership
  · exact packet_mem_of_chunk packets047_group packet1130_membership
  · exact packet_mem_of_chunk packets047_group packet1133_membership
  · exact packet_mem_of_chunk packets047_group packet1134_membership

def slice078Packets : List StripRowPacket :=
  [packet1035, packet1036, packet1037, packet1045, packet1046, packet1049,
   packet1050, packet1135, packet1137, packet1138, packet1147, packet1148,
   packet1151, packet1152, packet1192, packet1194, packet1198, packet1199]

def slice078 : GridSlice := closedSliceOfPackets 224 228 slice078Packets

private theorem slice078_checked_local : checkSlice slice078.vertical 64 slice078 = true := by
  decide +kernel

theorem slice078_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice078 = true := by
  apply sliceCheck_of_packets slice078_checked_local
  intro p hp
  simp only [slice078Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets043_group packet1035_membership
  · exact packet_mem_of_chunk packets043_group packet1036_membership
  · exact packet_mem_of_chunk packets043_group packet1037_membership
  · exact packet_mem_of_chunk packets043_group packet1045_membership
  · exact packet_mem_of_chunk packets043_group packet1046_membership
  · exact packet_mem_of_chunk packets043_group packet1049_membership
  · exact packet_mem_of_chunk packets043_group packet1050_membership
  · exact packet_mem_of_chunk packets047_group packet1135_membership
  · exact packet_mem_of_chunk packets047_group packet1137_membership
  · exact packet_mem_of_chunk packets047_group packet1138_membership
  · exact packet_mem_of_chunk packets047_group packet1147_membership
  · exact packet_mem_of_chunk packets047_group packet1148_membership
  · exact packet_mem_of_chunk packets047_group packet1151_membership
  · exact packet_mem_of_chunk packets048_group packet1152_membership
  · exact packet_mem_of_chunk packets049_group packet1192_membership
  · exact packet_mem_of_chunk packets049_group packet1194_membership
  · exact packet_mem_of_chunk packets049_group packet1198_membership
  · exact packet_mem_of_chunk packets049_group packet1199_membership

def slice079Packets : List StripRowPacket :=
  [packet1035, packet1036, packet1037, packet1045, packet1046, packet1049,
   packet1050, packet1136, packet1139, packet1140, packet1149, packet1150,
   packet1153, packet1154, packet1193, packet1194, packet1198, packet1199]

def slice079 : GridSlice := closedSliceOfPackets 228 232 slice079Packets

private theorem slice079_checked_local : checkSlice slice079.vertical 64 slice079 = true := by
  decide +kernel

theorem slice079_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice079 = true := by
  apply sliceCheck_of_packets slice079_checked_local
  intro p hp
  simp only [slice079Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets043_group packet1035_membership
  · exact packet_mem_of_chunk packets043_group packet1036_membership
  · exact packet_mem_of_chunk packets043_group packet1037_membership
  · exact packet_mem_of_chunk packets043_group packet1045_membership
  · exact packet_mem_of_chunk packets043_group packet1046_membership
  · exact packet_mem_of_chunk packets043_group packet1049_membership
  · exact packet_mem_of_chunk packets043_group packet1050_membership
  · exact packet_mem_of_chunk packets047_group packet1136_membership
  · exact packet_mem_of_chunk packets047_group packet1139_membership
  · exact packet_mem_of_chunk packets047_group packet1140_membership
  · exact packet_mem_of_chunk packets047_group packet1149_membership
  · exact packet_mem_of_chunk packets047_group packet1150_membership
  · exact packet_mem_of_chunk packets048_group packet1153_membership
  · exact packet_mem_of_chunk packets048_group packet1154_membership
  · exact packet_mem_of_chunk packets049_group packet1193_membership
  · exact packet_mem_of_chunk packets049_group packet1194_membership
  · exact packet_mem_of_chunk packets049_group packet1198_membership
  · exact packet_mem_of_chunk packets049_group packet1199_membership


end RKCert.ReviewedNative.ThreeInteriorPencil
