module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorLiteralStripRows

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

def slice008Packets : List StripRowPacket :=
  [packet0123, packet0125, packet0131, packet0133, packet0148, packet0149,
   packet0151, packet0152, packet0159, packet0160, packet0162, packet0163,
   packet0259, packet0261, packet0267, packet0269, packet0284, packet0285,
   packet0288, packet0289, packet0438, packet0440, packet0446, packet0448,
   packet0466, packet0467, packet0470, packet0471]

def slice008 : GridSlice := closedSliceOfPackets 8 9 slice008Packets

private theorem slice008_checked_local : checkSlice slice008.vertical 64 slice008 = true := by
  decide +kernel

theorem slice008_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice008 = true := by
  apply sliceCheck_of_packets slice008_checked_local
  intro p hp
  simp only [slice008Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets005_group packet0123_membership
  · exact packet_mem_of_chunk packets005_group packet0125_membership
  · exact packet_mem_of_chunk packets005_group packet0131_membership
  · exact packet_mem_of_chunk packets005_group packet0133_membership
  · exact packet_mem_of_chunk packets006_group packet0148_membership
  · exact packet_mem_of_chunk packets006_group packet0149_membership
  · exact packet_mem_of_chunk packets006_group packet0151_membership
  · exact packet_mem_of_chunk packets006_group packet0152_membership
  · exact packet_mem_of_chunk packets006_group packet0159_membership
  · exact packet_mem_of_chunk packets006_group packet0160_membership
  · exact packet_mem_of_chunk packets006_group packet0162_membership
  · exact packet_mem_of_chunk packets006_group packet0163_membership
  · exact packet_mem_of_chunk packets010_group packet0259_membership
  · exact packet_mem_of_chunk packets010_group packet0261_membership
  · exact packet_mem_of_chunk packets011_group packet0267_membership
  · exact packet_mem_of_chunk packets011_group packet0269_membership
  · exact packet_mem_of_chunk packets011_group packet0284_membership
  · exact packet_mem_of_chunk packets011_group packet0285_membership
  · exact packet_mem_of_chunk packets012_group packet0288_membership
  · exact packet_mem_of_chunk packets012_group packet0289_membership
  · exact packet_mem_of_chunk packets018_group packet0438_membership
  · exact packet_mem_of_chunk packets018_group packet0440_membership
  · exact packet_mem_of_chunk packets018_group packet0446_membership
  · exact packet_mem_of_chunk packets018_group packet0448_membership
  · exact packet_mem_of_chunk packets019_group packet0466_membership
  · exact packet_mem_of_chunk packets019_group packet0467_membership
  · exact packet_mem_of_chunk packets019_group packet0470_membership
  · exact packet_mem_of_chunk packets019_group packet0471_membership

def slice009Packets : List StripRowPacket :=
  [packet0124, packet0126, packet0132, packet0134, packet0150, packet0153,
   packet0154, packet0161, packet0164, packet0260, packet0262, packet0268,
   packet0270, packet0284, packet0285, packet0288, packet0289, packet0438,
   packet0440, packet0446, packet0448, packet0466, packet0467, packet0470,
   packet0471]

def slice009 : GridSlice := closedSliceOfPackets 9 10 slice009Packets

private theorem slice009_checked_local : checkSlice slice009.vertical 64 slice009 = true := by
  decide +kernel

theorem slice009_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice009 = true := by
  apply sliceCheck_of_packets slice009_checked_local
  intro p hp
  simp only [slice009Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets005_group packet0124_membership
  · exact packet_mem_of_chunk packets005_group packet0126_membership
  · exact packet_mem_of_chunk packets005_group packet0132_membership
  · exact packet_mem_of_chunk packets005_group packet0134_membership
  · exact packet_mem_of_chunk packets006_group packet0150_membership
  · exact packet_mem_of_chunk packets006_group packet0153_membership
  · exact packet_mem_of_chunk packets006_group packet0154_membership
  · exact packet_mem_of_chunk packets006_group packet0161_membership
  · exact packet_mem_of_chunk packets006_group packet0164_membership
  · exact packet_mem_of_chunk packets010_group packet0260_membership
  · exact packet_mem_of_chunk packets010_group packet0262_membership
  · exact packet_mem_of_chunk packets011_group packet0268_membership
  · exact packet_mem_of_chunk packets011_group packet0270_membership
  · exact packet_mem_of_chunk packets011_group packet0284_membership
  · exact packet_mem_of_chunk packets011_group packet0285_membership
  · exact packet_mem_of_chunk packets012_group packet0288_membership
  · exact packet_mem_of_chunk packets012_group packet0289_membership
  · exact packet_mem_of_chunk packets018_group packet0438_membership
  · exact packet_mem_of_chunk packets018_group packet0440_membership
  · exact packet_mem_of_chunk packets018_group packet0446_membership
  · exact packet_mem_of_chunk packets018_group packet0448_membership
  · exact packet_mem_of_chunk packets019_group packet0466_membership
  · exact packet_mem_of_chunk packets019_group packet0467_membership
  · exact packet_mem_of_chunk packets019_group packet0470_membership
  · exact packet_mem_of_chunk packets019_group packet0471_membership

def slice010Packets : List StripRowPacket :=
  [packet0127, packet0129, packet0135, packet0137, packet0155, packet0157,
   packet0165, packet0167, packet0263, packet0265, packet0271, packet0273,
   packet0286, packet0287, packet0290, packet0291, packet0439, packet0441,
   packet0447, packet0449, packet0466, packet0467, packet0470, packet0471]

def slice010 : GridSlice := closedSliceOfPackets 10 11 slice010Packets

private theorem slice010_checked_local : checkSlice slice010.vertical 64 slice010 = true := by
  decide +kernel

theorem slice010_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice010 = true := by
  apply sliceCheck_of_packets slice010_checked_local
  intro p hp
  simp only [slice010Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets005_group packet0127_membership
  · exact packet_mem_of_chunk packets005_group packet0129_membership
  · exact packet_mem_of_chunk packets005_group packet0135_membership
  · exact packet_mem_of_chunk packets005_group packet0137_membership
  · exact packet_mem_of_chunk packets006_group packet0155_membership
  · exact packet_mem_of_chunk packets006_group packet0157_membership
  · exact packet_mem_of_chunk packets006_group packet0165_membership
  · exact packet_mem_of_chunk packets006_group packet0167_membership
  · exact packet_mem_of_chunk packets010_group packet0263_membership
  · exact packet_mem_of_chunk packets011_group packet0265_membership
  · exact packet_mem_of_chunk packets011_group packet0271_membership
  · exact packet_mem_of_chunk packets011_group packet0273_membership
  · exact packet_mem_of_chunk packets011_group packet0286_membership
  · exact packet_mem_of_chunk packets011_group packet0287_membership
  · exact packet_mem_of_chunk packets012_group packet0290_membership
  · exact packet_mem_of_chunk packets012_group packet0291_membership
  · exact packet_mem_of_chunk packets018_group packet0439_membership
  · exact packet_mem_of_chunk packets018_group packet0441_membership
  · exact packet_mem_of_chunk packets018_group packet0447_membership
  · exact packet_mem_of_chunk packets018_group packet0449_membership
  · exact packet_mem_of_chunk packets019_group packet0466_membership
  · exact packet_mem_of_chunk packets019_group packet0467_membership
  · exact packet_mem_of_chunk packets019_group packet0470_membership
  · exact packet_mem_of_chunk packets019_group packet0471_membership

def slice011Packets : List StripRowPacket :=
  [packet0128, packet0130, packet0136, packet0138, packet0156, packet0158,
   packet0166, packet0168, packet0264, packet0266, packet0272, packet0273,
   packet0286, packet0287, packet0290, packet0291, packet0439, packet0441,
   packet0447, packet0449, packet0466, packet0467, packet0470, packet0471]

def slice011 : GridSlice := closedSliceOfPackets 11 12 slice011Packets

private theorem slice011_checked_local : checkSlice slice011.vertical 64 slice011 = true := by
  decide +kernel

theorem slice011_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice011 = true := by
  apply sliceCheck_of_packets slice011_checked_local
  intro p hp
  simp only [slice011Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets005_group packet0128_membership
  · exact packet_mem_of_chunk packets005_group packet0130_membership
  · exact packet_mem_of_chunk packets005_group packet0136_membership
  · exact packet_mem_of_chunk packets005_group packet0138_membership
  · exact packet_mem_of_chunk packets006_group packet0156_membership
  · exact packet_mem_of_chunk packets006_group packet0158_membership
  · exact packet_mem_of_chunk packets006_group packet0166_membership
  · exact packet_mem_of_chunk packets007_group packet0168_membership
  · exact packet_mem_of_chunk packets011_group packet0264_membership
  · exact packet_mem_of_chunk packets011_group packet0266_membership
  · exact packet_mem_of_chunk packets011_group packet0272_membership
  · exact packet_mem_of_chunk packets011_group packet0273_membership
  · exact packet_mem_of_chunk packets011_group packet0286_membership
  · exact packet_mem_of_chunk packets011_group packet0287_membership
  · exact packet_mem_of_chunk packets012_group packet0290_membership
  · exact packet_mem_of_chunk packets012_group packet0291_membership
  · exact packet_mem_of_chunk packets018_group packet0439_membership
  · exact packet_mem_of_chunk packets018_group packet0441_membership
  · exact packet_mem_of_chunk packets018_group packet0447_membership
  · exact packet_mem_of_chunk packets018_group packet0449_membership
  · exact packet_mem_of_chunk packets019_group packet0466_membership
  · exact packet_mem_of_chunk packets019_group packet0467_membership
  · exact packet_mem_of_chunk packets019_group packet0470_membership
  · exact packet_mem_of_chunk packets019_group packet0471_membership

def slice012Packets : List StripRowPacket :=
  [packet0139, packet0140, packet0143, packet0144, packet0169, packet0171,
   packet0175, packet0177, packet0274, packet0276, packet0280, packet0281,
   packet0292, packet0293, packet0296, packet0297, packet0442, packet0444,
   packet0450, packet0452, packet0468, packet0469, packet0472]

def slice012 : GridSlice := closedSliceOfPackets 12 13 slice012Packets

private theorem slice012_checked_local : checkSlice slice012.vertical 64 slice012 = true := by
  decide +kernel

theorem slice012_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice012 = true := by
  apply sliceCheck_of_packets slice012_checked_local
  intro p hp
  simp only [slice012Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets005_group packet0139_membership
  · exact packet_mem_of_chunk packets005_group packet0140_membership
  · exact packet_mem_of_chunk packets005_group packet0143_membership
  · exact packet_mem_of_chunk packets006_group packet0144_membership
  · exact packet_mem_of_chunk packets007_group packet0169_membership
  · exact packet_mem_of_chunk packets007_group packet0171_membership
  · exact packet_mem_of_chunk packets007_group packet0175_membership
  · exact packet_mem_of_chunk packets007_group packet0177_membership
  · exact packet_mem_of_chunk packets011_group packet0274_membership
  · exact packet_mem_of_chunk packets011_group packet0276_membership
  · exact packet_mem_of_chunk packets011_group packet0280_membership
  · exact packet_mem_of_chunk packets011_group packet0281_membership
  · exact packet_mem_of_chunk packets012_group packet0292_membership
  · exact packet_mem_of_chunk packets012_group packet0293_membership
  · exact packet_mem_of_chunk packets012_group packet0296_membership
  · exact packet_mem_of_chunk packets012_group packet0297_membership
  · exact packet_mem_of_chunk packets018_group packet0442_membership
  · exact packet_mem_of_chunk packets018_group packet0444_membership
  · exact packet_mem_of_chunk packets018_group packet0450_membership
  · exact packet_mem_of_chunk packets018_group packet0452_membership
  · exact packet_mem_of_chunk packets019_group packet0468_membership
  · exact packet_mem_of_chunk packets019_group packet0469_membership
  · exact packet_mem_of_chunk packets019_group packet0472_membership

def slice013Packets : List StripRowPacket :=
  [packet0139, packet0140, packet0143, packet0145, packet0170, packet0172,
   packet0176, packet0178, packet0275, packet0277, packet0280, packet0281,
   packet0292, packet0293, packet0296, packet0297, packet0442, packet0444,
   packet0450, packet0452, packet0468, packet0469, packet0472]

def slice013 : GridSlice := closedSliceOfPackets 13 14 slice013Packets

private theorem slice013_checked_local : checkSlice slice013.vertical 64 slice013 = true := by
  decide +kernel

theorem slice013_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice013 = true := by
  apply sliceCheck_of_packets slice013_checked_local
  intro p hp
  simp only [slice013Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets005_group packet0139_membership
  · exact packet_mem_of_chunk packets005_group packet0140_membership
  · exact packet_mem_of_chunk packets005_group packet0143_membership
  · exact packet_mem_of_chunk packets006_group packet0145_membership
  · exact packet_mem_of_chunk packets007_group packet0170_membership
  · exact packet_mem_of_chunk packets007_group packet0172_membership
  · exact packet_mem_of_chunk packets007_group packet0176_membership
  · exact packet_mem_of_chunk packets007_group packet0178_membership
  · exact packet_mem_of_chunk packets011_group packet0275_membership
  · exact packet_mem_of_chunk packets011_group packet0277_membership
  · exact packet_mem_of_chunk packets011_group packet0280_membership
  · exact packet_mem_of_chunk packets011_group packet0281_membership
  · exact packet_mem_of_chunk packets012_group packet0292_membership
  · exact packet_mem_of_chunk packets012_group packet0293_membership
  · exact packet_mem_of_chunk packets012_group packet0296_membership
  · exact packet_mem_of_chunk packets012_group packet0297_membership
  · exact packet_mem_of_chunk packets018_group packet0442_membership
  · exact packet_mem_of_chunk packets018_group packet0444_membership
  · exact packet_mem_of_chunk packets018_group packet0450_membership
  · exact packet_mem_of_chunk packets018_group packet0452_membership
  · exact packet_mem_of_chunk packets019_group packet0468_membership
  · exact packet_mem_of_chunk packets019_group packet0469_membership
  · exact packet_mem_of_chunk packets019_group packet0472_membership

def slice014Packets : List StripRowPacket :=
  [packet0141, packet0142, packet0146, packet0147, packet0173, packet0174,
   packet0179, packet0180, packet0278, packet0279, packet0282, packet0283,
   packet0294, packet0295, packet0298, packet0299, packet0443, packet0445,
   packet0451, packet0453, packet0468, packet0469, packet0472]

def slice014 : GridSlice := closedSliceOfPackets 14 15 slice014Packets

private theorem slice014_checked_local : checkSlice slice014.vertical 64 slice014 = true := by
  decide +kernel

theorem slice014_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice014 = true := by
  apply sliceCheck_of_packets slice014_checked_local
  intro p hp
  simp only [slice014Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets005_group packet0141_membership
  · exact packet_mem_of_chunk packets005_group packet0142_membership
  · exact packet_mem_of_chunk packets006_group packet0146_membership
  · exact packet_mem_of_chunk packets006_group packet0147_membership
  · exact packet_mem_of_chunk packets007_group packet0173_membership
  · exact packet_mem_of_chunk packets007_group packet0174_membership
  · exact packet_mem_of_chunk packets007_group packet0179_membership
  · exact packet_mem_of_chunk packets007_group packet0180_membership
  · exact packet_mem_of_chunk packets011_group packet0278_membership
  · exact packet_mem_of_chunk packets011_group packet0279_membership
  · exact packet_mem_of_chunk packets011_group packet0282_membership
  · exact packet_mem_of_chunk packets011_group packet0283_membership
  · exact packet_mem_of_chunk packets012_group packet0294_membership
  · exact packet_mem_of_chunk packets012_group packet0295_membership
  · exact packet_mem_of_chunk packets012_group packet0298_membership
  · exact packet_mem_of_chunk packets012_group packet0299_membership
  · exact packet_mem_of_chunk packets018_group packet0443_membership
  · exact packet_mem_of_chunk packets018_group packet0445_membership
  · exact packet_mem_of_chunk packets018_group packet0451_membership
  · exact packet_mem_of_chunk packets018_group packet0453_membership
  · exact packet_mem_of_chunk packets019_group packet0468_membership
  · exact packet_mem_of_chunk packets019_group packet0469_membership
  · exact packet_mem_of_chunk packets019_group packet0472_membership

def slice015Packets : List StripRowPacket :=
  [packet0141, packet0142, packet0146, packet0147, packet0173, packet0174,
   packet0179, packet0181, packet0278, packet0279, packet0282, packet0283,
   packet0294, packet0295, packet0298, packet0299, packet0443, packet0445,
   packet0451, packet0453, packet0468, packet0469, packet0472]

def slice015 : GridSlice := closedSliceOfPackets 15 16 slice015Packets

private theorem slice015_checked_local : checkSlice slice015.vertical 64 slice015 = true := by
  decide +kernel

theorem slice015_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice015 = true := by
  apply sliceCheck_of_packets slice015_checked_local
  intro p hp
  simp only [slice015Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets005_group packet0141_membership
  · exact packet_mem_of_chunk packets005_group packet0142_membership
  · exact packet_mem_of_chunk packets006_group packet0146_membership
  · exact packet_mem_of_chunk packets006_group packet0147_membership
  · exact packet_mem_of_chunk packets007_group packet0173_membership
  · exact packet_mem_of_chunk packets007_group packet0174_membership
  · exact packet_mem_of_chunk packets007_group packet0179_membership
  · exact packet_mem_of_chunk packets007_group packet0181_membership
  · exact packet_mem_of_chunk packets011_group packet0278_membership
  · exact packet_mem_of_chunk packets011_group packet0279_membership
  · exact packet_mem_of_chunk packets011_group packet0282_membership
  · exact packet_mem_of_chunk packets011_group packet0283_membership
  · exact packet_mem_of_chunk packets012_group packet0294_membership
  · exact packet_mem_of_chunk packets012_group packet0295_membership
  · exact packet_mem_of_chunk packets012_group packet0298_membership
  · exact packet_mem_of_chunk packets012_group packet0299_membership
  · exact packet_mem_of_chunk packets018_group packet0443_membership
  · exact packet_mem_of_chunk packets018_group packet0445_membership
  · exact packet_mem_of_chunk packets018_group packet0451_membership
  · exact packet_mem_of_chunk packets018_group packet0453_membership
  · exact packet_mem_of_chunk packets019_group packet0468_membership
  · exact packet_mem_of_chunk packets019_group packet0469_membership
  · exact packet_mem_of_chunk packets019_group packet0472_membership


end RKCert.ReviewedNative.ThreeInteriorPencil
