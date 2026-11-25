module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorLiteralStripRows

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

def slice064Packets : List StripRowPacket :=
  [packet0875, packet0878, packet0879, packet0887, packet0888, packet0891,
   packet0892, packet0953, packet0955, packet0963, packet0964, packet0967,
   packet0994, packet0995, packet0998, packet0999]

def slice064 : GridSlice := closedSliceOfPackets 168 172 slice064Packets

private theorem slice064_checked_local : checkSlice slice064.vertical 64 slice064 = true := by
  decide +kernel

theorem slice064_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice064 = true := by
  apply sliceCheck_of_packets slice064_checked_local
  intro p hp
  simp only [slice064Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets036_group packet0875_membership
  · exact packet_mem_of_chunk packets036_group packet0878_membership
  · exact packet_mem_of_chunk packets036_group packet0879_membership
  · exact packet_mem_of_chunk packets036_group packet0887_membership
  · exact packet_mem_of_chunk packets037_group packet0888_membership
  · exact packet_mem_of_chunk packets037_group packet0891_membership
  · exact packet_mem_of_chunk packets037_group packet0892_membership
  · exact packet_mem_of_chunk packets039_group packet0953_membership
  · exact packet_mem_of_chunk packets039_group packet0955_membership
  · exact packet_mem_of_chunk packets040_group packet0963_membership
  · exact packet_mem_of_chunk packets040_group packet0964_membership
  · exact packet_mem_of_chunk packets040_group packet0967_membership
  · exact packet_mem_of_chunk packets041_group packet0994_membership
  · exact packet_mem_of_chunk packets041_group packet0995_membership
  · exact packet_mem_of_chunk packets041_group packet0998_membership
  · exact packet_mem_of_chunk packets041_group packet0999_membership

def slice065Packets : List StripRowPacket :=
  [packet0875, packet0878, packet0879, packet0887, packet0888, packet0891,
   packet0892, packet0954, packet0956, packet0965, packet0966, packet0968,
   packet0994, packet0995, packet0998, packet0999]

def slice065 : GridSlice := closedSliceOfPackets 172 176 slice065Packets

private theorem slice065_checked_local : checkSlice slice065.vertical 64 slice065 = true := by
  decide +kernel

theorem slice065_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice065 = true := by
  apply sliceCheck_of_packets slice065_checked_local
  intro p hp
  simp only [slice065Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets036_group packet0875_membership
  · exact packet_mem_of_chunk packets036_group packet0878_membership
  · exact packet_mem_of_chunk packets036_group packet0879_membership
  · exact packet_mem_of_chunk packets036_group packet0887_membership
  · exact packet_mem_of_chunk packets037_group packet0888_membership
  · exact packet_mem_of_chunk packets037_group packet0891_membership
  · exact packet_mem_of_chunk packets037_group packet0892_membership
  · exact packet_mem_of_chunk packets039_group packet0954_membership
  · exact packet_mem_of_chunk packets039_group packet0956_membership
  · exact packet_mem_of_chunk packets040_group packet0965_membership
  · exact packet_mem_of_chunk packets040_group packet0966_membership
  · exact packet_mem_of_chunk packets040_group packet0968_membership
  · exact packet_mem_of_chunk packets041_group packet0994_membership
  · exact packet_mem_of_chunk packets041_group packet0995_membership
  · exact packet_mem_of_chunk packets041_group packet0998_membership
  · exact packet_mem_of_chunk packets041_group packet0999_membership

def slice066Packets : List StripRowPacket :=
  [packet0880, packet0881, packet0882, packet0893, packet0894, packet0897,
   packet0898, packet0969, packet0971, packet0980, packet0981, packet0984,
   packet1000, packet1002, packet1006, packet1007]

def slice066 : GridSlice := closedSliceOfPackets 176 180 slice066Packets

private theorem slice066_checked_local : checkSlice slice066.vertical 64 slice066 = true := by
  decide +kernel

theorem slice066_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice066 = true := by
  apply sliceCheck_of_packets slice066_checked_local
  intro p hp
  simp only [slice066Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets036_group packet0880_membership
  · exact packet_mem_of_chunk packets036_group packet0881_membership
  · exact packet_mem_of_chunk packets036_group packet0882_membership
  · exact packet_mem_of_chunk packets037_group packet0893_membership
  · exact packet_mem_of_chunk packets037_group packet0894_membership
  · exact packet_mem_of_chunk packets037_group packet0897_membership
  · exact packet_mem_of_chunk packets037_group packet0898_membership
  · exact packet_mem_of_chunk packets040_group packet0969_membership
  · exact packet_mem_of_chunk packets040_group packet0971_membership
  · exact packet_mem_of_chunk packets040_group packet0980_membership
  · exact packet_mem_of_chunk packets040_group packet0981_membership
  · exact packet_mem_of_chunk packets041_group packet0984_membership
  · exact packet_mem_of_chunk packets041_group packet1000_membership
  · exact packet_mem_of_chunk packets041_group packet1002_membership
  · exact packet_mem_of_chunk packets041_group packet1006_membership
  · exact packet_mem_of_chunk packets041_group packet1007_membership

def slice067Packets : List StripRowPacket :=
  [packet0880, packet0881, packet0882, packet0893, packet0894, packet0897,
   packet0898, packet0970, packet0972, packet0973, packet0982, packet0983,
   packet0985, packet1001, packet1002, packet1006, packet1007]

def slice067 : GridSlice := closedSliceOfPackets 180 184 slice067Packets

private theorem slice067_checked_local : checkSlice slice067.vertical 64 slice067 = true := by
  decide +kernel

theorem slice067_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice067 = true := by
  apply sliceCheck_of_packets slice067_checked_local
  intro p hp
  simp only [slice067Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets036_group packet0880_membership
  · exact packet_mem_of_chunk packets036_group packet0881_membership
  · exact packet_mem_of_chunk packets036_group packet0882_membership
  · exact packet_mem_of_chunk packets037_group packet0893_membership
  · exact packet_mem_of_chunk packets037_group packet0894_membership
  · exact packet_mem_of_chunk packets037_group packet0897_membership
  · exact packet_mem_of_chunk packets037_group packet0898_membership
  · exact packet_mem_of_chunk packets040_group packet0970_membership
  · exact packet_mem_of_chunk packets040_group packet0972_membership
  · exact packet_mem_of_chunk packets040_group packet0973_membership
  · exact packet_mem_of_chunk packets040_group packet0982_membership
  · exact packet_mem_of_chunk packets040_group packet0983_membership
  · exact packet_mem_of_chunk packets041_group packet0985_membership
  · exact packet_mem_of_chunk packets041_group packet1001_membership
  · exact packet_mem_of_chunk packets041_group packet1002_membership
  · exact packet_mem_of_chunk packets041_group packet1006_membership
  · exact packet_mem_of_chunk packets041_group packet1007_membership

def slice068Packets : List StripRowPacket :=
  [packet0880, packet0883, packet0884, packet0895, packet0896, packet0899,
   packet0900, packet0974, packet0976, packet0977, packet0986, packet0987,
   packet0990, packet1003, packet1005, packet1008, packet1009]

def slice068 : GridSlice := closedSliceOfPackets 184 188 slice068Packets

private theorem slice068_checked_local : checkSlice slice068.vertical 64 slice068 = true := by
  decide +kernel

theorem slice068_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice068 = true := by
  apply sliceCheck_of_packets slice068_checked_local
  intro p hp
  simp only [slice068Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets036_group packet0880_membership
  · exact packet_mem_of_chunk packets036_group packet0883_membership
  · exact packet_mem_of_chunk packets036_group packet0884_membership
  · exact packet_mem_of_chunk packets037_group packet0895_membership
  · exact packet_mem_of_chunk packets037_group packet0896_membership
  · exact packet_mem_of_chunk packets037_group packet0899_membership
  · exact packet_mem_of_chunk packets037_group packet0900_membership
  · exact packet_mem_of_chunk packets040_group packet0974_membership
  · exact packet_mem_of_chunk packets040_group packet0976_membership
  · exact packet_mem_of_chunk packets040_group packet0977_membership
  · exact packet_mem_of_chunk packets041_group packet0986_membership
  · exact packet_mem_of_chunk packets041_group packet0987_membership
  · exact packet_mem_of_chunk packets041_group packet0990_membership
  · exact packet_mem_of_chunk packets041_group packet1003_membership
  · exact packet_mem_of_chunk packets041_group packet1005_membership
  · exact packet_mem_of_chunk packets042_group packet1008_membership
  · exact packet_mem_of_chunk packets042_group packet1009_membership

def slice069Packets : List StripRowPacket :=
  [packet0880, packet0883, packet0884, packet0895, packet0896, packet0899,
   packet0900, packet0975, packet0978, packet0979, packet0988, packet0989,
   packet0991, packet1004, packet1005, packet1008, packet1009]

def slice069 : GridSlice := closedSliceOfPackets 188 192 slice069Packets

private theorem slice069_checked_local : checkSlice slice069.vertical 64 slice069 = true := by
  decide +kernel

theorem slice069_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice069 = true := by
  apply sliceCheck_of_packets slice069_checked_local
  intro p hp
  simp only [slice069Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets036_group packet0880_membership
  · exact packet_mem_of_chunk packets036_group packet0883_membership
  · exact packet_mem_of_chunk packets036_group packet0884_membership
  · exact packet_mem_of_chunk packets037_group packet0895_membership
  · exact packet_mem_of_chunk packets037_group packet0896_membership
  · exact packet_mem_of_chunk packets037_group packet0899_membership
  · exact packet_mem_of_chunk packets037_group packet0900_membership
  · exact packet_mem_of_chunk packets040_group packet0975_membership
  · exact packet_mem_of_chunk packets040_group packet0978_membership
  · exact packet_mem_of_chunk packets040_group packet0979_membership
  · exact packet_mem_of_chunk packets041_group packet0988_membership
  · exact packet_mem_of_chunk packets041_group packet0989_membership
  · exact packet_mem_of_chunk packets041_group packet0991_membership
  · exact packet_mem_of_chunk packets041_group packet1004_membership
  · exact packet_mem_of_chunk packets041_group packet1005_membership
  · exact packet_mem_of_chunk packets042_group packet1008_membership
  · exact packet_mem_of_chunk packets042_group packet1009_membership

def slice070Packets : List StripRowPacket :=
  [packet1010, packet1011, packet1019, packet1020, packet1023, packet1024,
   packet1061, packet1063, packet1064, packet1073, packet1074, packet1077,
   packet1115, packet1117, packet1121, packet1122]

def slice070 : GridSlice := closedSliceOfPackets 192 196 slice070Packets

private theorem slice070_checked_local : checkSlice slice070.vertical 64 slice070 = true := by
  decide +kernel

theorem slice070_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice070 = true := by
  apply sliceCheck_of_packets slice070_checked_local
  intro p hp
  simp only [slice070Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets042_group packet1010_membership
  · exact packet_mem_of_chunk packets042_group packet1011_membership
  · exact packet_mem_of_chunk packets042_group packet1019_membership
  · exact packet_mem_of_chunk packets042_group packet1020_membership
  · exact packet_mem_of_chunk packets042_group packet1023_membership
  · exact packet_mem_of_chunk packets042_group packet1024_membership
  · exact packet_mem_of_chunk packets044_group packet1061_membership
  · exact packet_mem_of_chunk packets044_group packet1063_membership
  · exact packet_mem_of_chunk packets044_group packet1064_membership
  · exact packet_mem_of_chunk packets044_group packet1073_membership
  · exact packet_mem_of_chunk packets044_group packet1074_membership
  · exact packet_mem_of_chunk packets044_group packet1077_membership
  · exact packet_mem_of_chunk packets046_group packet1115_membership
  · exact packet_mem_of_chunk packets046_group packet1117_membership
  · exact packet_mem_of_chunk packets046_group packet1121_membership
  · exact packet_mem_of_chunk packets046_group packet1122_membership

def slice071Packets : List StripRowPacket :=
  [packet1010, packet1011, packet1019, packet1020, packet1023, packet1024,
   packet1062, packet1065, packet1066, packet1075, packet1076, packet1078,
   packet1116, packet1117, packet1121, packet1122]

def slice071 : GridSlice := closedSliceOfPackets 196 200 slice071Packets

private theorem slice071_checked_local : checkSlice slice071.vertical 64 slice071 = true := by
  decide +kernel

theorem slice071_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice071 = true := by
  apply sliceCheck_of_packets slice071_checked_local
  intro p hp
  simp only [slice071Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets042_group packet1010_membership
  · exact packet_mem_of_chunk packets042_group packet1011_membership
  · exact packet_mem_of_chunk packets042_group packet1019_membership
  · exact packet_mem_of_chunk packets042_group packet1020_membership
  · exact packet_mem_of_chunk packets042_group packet1023_membership
  · exact packet_mem_of_chunk packets042_group packet1024_membership
  · exact packet_mem_of_chunk packets044_group packet1062_membership
  · exact packet_mem_of_chunk packets044_group packet1065_membership
  · exact packet_mem_of_chunk packets044_group packet1066_membership
  · exact packet_mem_of_chunk packets044_group packet1075_membership
  · exact packet_mem_of_chunk packets044_group packet1076_membership
  · exact packet_mem_of_chunk packets044_group packet1078_membership
  · exact packet_mem_of_chunk packets046_group packet1116_membership
  · exact packet_mem_of_chunk packets046_group packet1117_membership
  · exact packet_mem_of_chunk packets046_group packet1121_membership
  · exact packet_mem_of_chunk packets046_group packet1122_membership


end RKCert.ReviewedNative.ThreeInteriorPencil
