module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorLiteralStripRows

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

def slice000Packets : List StripRowPacket :=
  [packet0000, packet0001, packet0004, packet0005, packet0016, packet0017,
   packet0020, packet0021, packet0059, packet0060, packet0063, packet0064,
   packet0075, packet0076, packet0079, packet0080, packet0182, packet0183,
   packet0186, packet0187, packet0198, packet0199, packet0202, packet0203,
   packet0236, packet0237, packet0239, packet0245, packet0247, packet0416,
   packet0417, packet0420, packet0421, packet0428, packet0429, packet0431,
   packet0432, packet0454, packet0456, packet0461, packet0463]

def slice000 : GridSlice := closedSliceOfPackets 0 1 slice000Packets

private theorem slice000_checked_local : checkSlice slice000.vertical 64 slice000 = true := by
  decide +kernel

theorem slice000_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice000 = true := by
  apply sliceCheck_of_packets slice000_checked_local
  intro p hp
  simp only [slice000Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets000_group packet0000_membership
  · exact packet_mem_of_chunk packets000_group packet0001_membership
  · exact packet_mem_of_chunk packets000_group packet0004_membership
  · exact packet_mem_of_chunk packets000_group packet0005_membership
  · exact packet_mem_of_chunk packets000_group packet0016_membership
  · exact packet_mem_of_chunk packets000_group packet0017_membership
  · exact packet_mem_of_chunk packets000_group packet0020_membership
  · exact packet_mem_of_chunk packets000_group packet0021_membership
  · exact packet_mem_of_chunk packets002_group packet0059_membership
  · exact packet_mem_of_chunk packets002_group packet0060_membership
  · exact packet_mem_of_chunk packets002_group packet0063_membership
  · exact packet_mem_of_chunk packets002_group packet0064_membership
  · exact packet_mem_of_chunk packets003_group packet0075_membership
  · exact packet_mem_of_chunk packets003_group packet0076_membership
  · exact packet_mem_of_chunk packets003_group packet0079_membership
  · exact packet_mem_of_chunk packets003_group packet0080_membership
  · exact packet_mem_of_chunk packets007_group packet0182_membership
  · exact packet_mem_of_chunk packets007_group packet0183_membership
  · exact packet_mem_of_chunk packets007_group packet0186_membership
  · exact packet_mem_of_chunk packets007_group packet0187_membership
  · exact packet_mem_of_chunk packets008_group packet0198_membership
  · exact packet_mem_of_chunk packets008_group packet0199_membership
  · exact packet_mem_of_chunk packets008_group packet0202_membership
  · exact packet_mem_of_chunk packets008_group packet0203_membership
  · exact packet_mem_of_chunk packets009_group packet0236_membership
  · exact packet_mem_of_chunk packets009_group packet0237_membership
  · exact packet_mem_of_chunk packets009_group packet0239_membership
  · exact packet_mem_of_chunk packets010_group packet0245_membership
  · exact packet_mem_of_chunk packets010_group packet0247_membership
  · exact packet_mem_of_chunk packets017_group packet0416_membership
  · exact packet_mem_of_chunk packets017_group packet0417_membership
  · exact packet_mem_of_chunk packets017_group packet0420_membership
  · exact packet_mem_of_chunk packets017_group packet0421_membership
  · exact packet_mem_of_chunk packets017_group packet0428_membership
  · exact packet_mem_of_chunk packets017_group packet0429_membership
  · exact packet_mem_of_chunk packets017_group packet0431_membership
  · exact packet_mem_of_chunk packets018_group packet0432_membership
  · exact packet_mem_of_chunk packets018_group packet0454_membership
  · exact packet_mem_of_chunk packets019_group packet0456_membership
  · exact packet_mem_of_chunk packets019_group packet0461_membership
  · exact packet_mem_of_chunk packets019_group packet0463_membership

def slice001Packets : List StripRowPacket :=
  [packet0002, packet0003, packet0006, packet0007, packet0018, packet0019,
   packet0022, packet0023, packet0061, packet0062, packet0065, packet0066,
   packet0077, packet0078, packet0081, packet0082, packet0184, packet0185,
   packet0188, packet0189, packet0200, packet0201, packet0204, packet0205,
   packet0238, packet0240, packet0246, packet0247, packet0416, packet0417,
   packet0420, packet0421, packet0428, packet0429, packet0431, packet0432,
   packet0454, packet0456, packet0461, packet0463]

def slice001 : GridSlice := closedSliceOfPackets 1 2 slice001Packets

private theorem slice001_checked_local : checkSlice slice001.vertical 64 slice001 = true := by
  decide +kernel

theorem slice001_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice001 = true := by
  apply sliceCheck_of_packets slice001_checked_local
  intro p hp
  simp only [slice001Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets000_group packet0002_membership
  · exact packet_mem_of_chunk packets000_group packet0003_membership
  · exact packet_mem_of_chunk packets000_group packet0006_membership
  · exact packet_mem_of_chunk packets000_group packet0007_membership
  · exact packet_mem_of_chunk packets000_group packet0018_membership
  · exact packet_mem_of_chunk packets000_group packet0019_membership
  · exact packet_mem_of_chunk packets000_group packet0022_membership
  · exact packet_mem_of_chunk packets000_group packet0023_membership
  · exact packet_mem_of_chunk packets002_group packet0061_membership
  · exact packet_mem_of_chunk packets002_group packet0062_membership
  · exact packet_mem_of_chunk packets002_group packet0065_membership
  · exact packet_mem_of_chunk packets002_group packet0066_membership
  · exact packet_mem_of_chunk packets003_group packet0077_membership
  · exact packet_mem_of_chunk packets003_group packet0078_membership
  · exact packet_mem_of_chunk packets003_group packet0081_membership
  · exact packet_mem_of_chunk packets003_group packet0082_membership
  · exact packet_mem_of_chunk packets007_group packet0184_membership
  · exact packet_mem_of_chunk packets007_group packet0185_membership
  · exact packet_mem_of_chunk packets007_group packet0188_membership
  · exact packet_mem_of_chunk packets007_group packet0189_membership
  · exact packet_mem_of_chunk packets008_group packet0200_membership
  · exact packet_mem_of_chunk packets008_group packet0201_membership
  · exact packet_mem_of_chunk packets008_group packet0204_membership
  · exact packet_mem_of_chunk packets008_group packet0205_membership
  · exact packet_mem_of_chunk packets009_group packet0238_membership
  · exact packet_mem_of_chunk packets010_group packet0240_membership
  · exact packet_mem_of_chunk packets010_group packet0246_membership
  · exact packet_mem_of_chunk packets010_group packet0247_membership
  · exact packet_mem_of_chunk packets017_group packet0416_membership
  · exact packet_mem_of_chunk packets017_group packet0417_membership
  · exact packet_mem_of_chunk packets017_group packet0420_membership
  · exact packet_mem_of_chunk packets017_group packet0421_membership
  · exact packet_mem_of_chunk packets017_group packet0428_membership
  · exact packet_mem_of_chunk packets017_group packet0429_membership
  · exact packet_mem_of_chunk packets017_group packet0431_membership
  · exact packet_mem_of_chunk packets018_group packet0432_membership
  · exact packet_mem_of_chunk packets018_group packet0454_membership
  · exact packet_mem_of_chunk packets019_group packet0456_membership
  · exact packet_mem_of_chunk packets019_group packet0461_membership
  · exact packet_mem_of_chunk packets019_group packet0463_membership

def slice002Packets : List StripRowPacket :=
  [packet0008, packet0009, packet0012, packet0013, packet0024, packet0025,
   packet0028, packet0029, packet0067, packet0068, packet0071, packet0072,
   packet0083, packet0084, packet0087, packet0088, packet0190, packet0191,
   packet0194, packet0195, packet0206, packet0207, packet0210, packet0241,
   packet0243, packet0248, packet0249, packet0418, packet0419, packet0422,
   packet0430, packet0433, packet0455, packet0457, packet0462, packet0463]

def slice002 : GridSlice := closedSliceOfPackets 2 3 slice002Packets

private theorem slice002_checked_local : checkSlice slice002.vertical 64 slice002 = true := by
  decide +kernel

theorem slice002_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice002 = true := by
  apply sliceCheck_of_packets slice002_checked_local
  intro p hp
  simp only [slice002Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets000_group packet0008_membership
  · exact packet_mem_of_chunk packets000_group packet0009_membership
  · exact packet_mem_of_chunk packets000_group packet0012_membership
  · exact packet_mem_of_chunk packets000_group packet0013_membership
  · exact packet_mem_of_chunk packets001_group packet0024_membership
  · exact packet_mem_of_chunk packets001_group packet0025_membership
  · exact packet_mem_of_chunk packets001_group packet0028_membership
  · exact packet_mem_of_chunk packets001_group packet0029_membership
  · exact packet_mem_of_chunk packets002_group packet0067_membership
  · exact packet_mem_of_chunk packets002_group packet0068_membership
  · exact packet_mem_of_chunk packets002_group packet0071_membership
  · exact packet_mem_of_chunk packets003_group packet0072_membership
  · exact packet_mem_of_chunk packets003_group packet0083_membership
  · exact packet_mem_of_chunk packets003_group packet0084_membership
  · exact packet_mem_of_chunk packets003_group packet0087_membership
  · exact packet_mem_of_chunk packets003_group packet0088_membership
  · exact packet_mem_of_chunk packets007_group packet0190_membership
  · exact packet_mem_of_chunk packets007_group packet0191_membership
  · exact packet_mem_of_chunk packets008_group packet0194_membership
  · exact packet_mem_of_chunk packets008_group packet0195_membership
  · exact packet_mem_of_chunk packets008_group packet0206_membership
  · exact packet_mem_of_chunk packets008_group packet0207_membership
  · exact packet_mem_of_chunk packets008_group packet0210_membership
  · exact packet_mem_of_chunk packets010_group packet0241_membership
  · exact packet_mem_of_chunk packets010_group packet0243_membership
  · exact packet_mem_of_chunk packets010_group packet0248_membership
  · exact packet_mem_of_chunk packets010_group packet0249_membership
  · exact packet_mem_of_chunk packets017_group packet0418_membership
  · exact packet_mem_of_chunk packets017_group packet0419_membership
  · exact packet_mem_of_chunk packets017_group packet0422_membership
  · exact packet_mem_of_chunk packets017_group packet0430_membership
  · exact packet_mem_of_chunk packets018_group packet0433_membership
  · exact packet_mem_of_chunk packets018_group packet0455_membership
  · exact packet_mem_of_chunk packets019_group packet0457_membership
  · exact packet_mem_of_chunk packets019_group packet0462_membership
  · exact packet_mem_of_chunk packets019_group packet0463_membership

def slice003Packets : List StripRowPacket :=
  [packet0010, packet0011, packet0014, packet0015, packet0026, packet0027,
   packet0030, packet0031, packet0069, packet0070, packet0073, packet0074,
   packet0085, packet0086, packet0089, packet0090, packet0192, packet0193,
   packet0196, packet0197, packet0208, packet0209, packet0211, packet0242,
   packet0244, packet0248, packet0249, packet0418, packet0419, packet0422,
   packet0430, packet0433, packet0455, packet0457, packet0462, packet0463]

def slice003 : GridSlice := closedSliceOfPackets 3 4 slice003Packets

private theorem slice003_checked_local : checkSlice slice003.vertical 64 slice003 = true := by
  decide +kernel

theorem slice003_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice003 = true := by
  apply sliceCheck_of_packets slice003_checked_local
  intro p hp
  simp only [slice003Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets000_group packet0010_membership
  · exact packet_mem_of_chunk packets000_group packet0011_membership
  · exact packet_mem_of_chunk packets000_group packet0014_membership
  · exact packet_mem_of_chunk packets000_group packet0015_membership
  · exact packet_mem_of_chunk packets001_group packet0026_membership
  · exact packet_mem_of_chunk packets001_group packet0027_membership
  · exact packet_mem_of_chunk packets001_group packet0030_membership
  · exact packet_mem_of_chunk packets001_group packet0031_membership
  · exact packet_mem_of_chunk packets002_group packet0069_membership
  · exact packet_mem_of_chunk packets002_group packet0070_membership
  · exact packet_mem_of_chunk packets003_group packet0073_membership
  · exact packet_mem_of_chunk packets003_group packet0074_membership
  · exact packet_mem_of_chunk packets003_group packet0085_membership
  · exact packet_mem_of_chunk packets003_group packet0086_membership
  · exact packet_mem_of_chunk packets003_group packet0089_membership
  · exact packet_mem_of_chunk packets003_group packet0090_membership
  · exact packet_mem_of_chunk packets008_group packet0192_membership
  · exact packet_mem_of_chunk packets008_group packet0193_membership
  · exact packet_mem_of_chunk packets008_group packet0196_membership
  · exact packet_mem_of_chunk packets008_group packet0197_membership
  · exact packet_mem_of_chunk packets008_group packet0208_membership
  · exact packet_mem_of_chunk packets008_group packet0209_membership
  · exact packet_mem_of_chunk packets008_group packet0211_membership
  · exact packet_mem_of_chunk packets010_group packet0242_membership
  · exact packet_mem_of_chunk packets010_group packet0244_membership
  · exact packet_mem_of_chunk packets010_group packet0248_membership
  · exact packet_mem_of_chunk packets010_group packet0249_membership
  · exact packet_mem_of_chunk packets017_group packet0418_membership
  · exact packet_mem_of_chunk packets017_group packet0419_membership
  · exact packet_mem_of_chunk packets017_group packet0422_membership
  · exact packet_mem_of_chunk packets017_group packet0430_membership
  · exact packet_mem_of_chunk packets018_group packet0433_membership
  · exact packet_mem_of_chunk packets018_group packet0455_membership
  · exact packet_mem_of_chunk packets019_group packet0457_membership
  · exact packet_mem_of_chunk packets019_group packet0462_membership
  · exact packet_mem_of_chunk packets019_group packet0463_membership

def slice004Packets : List StripRowPacket :=
  [packet0032, packet0033, packet0036, packet0037, packet0044, packet0045,
   packet0048, packet0049, packet0091, packet0092, packet0095, packet0096,
   packet0107, packet0108, packet0111, packet0112, packet0212, packet0213,
   packet0216, packet0217, packet0227, packet0228, packet0230, packet0250,
   packet0252, packet0255, packet0256, packet0423, packet0424, packet0426,
   packet0434, packet0436, packet0458, packet0460, packet0464, packet0465]

def slice004 : GridSlice := closedSliceOfPackets 4 5 slice004Packets

private theorem slice004_checked_local : checkSlice slice004.vertical 64 slice004 = true := by
  decide +kernel

theorem slice004_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice004 = true := by
  apply sliceCheck_of_packets slice004_checked_local
  intro p hp
  simp only [slice004Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets001_group packet0032_membership
  · exact packet_mem_of_chunk packets001_group packet0033_membership
  · exact packet_mem_of_chunk packets001_group packet0036_membership
  · exact packet_mem_of_chunk packets001_group packet0037_membership
  · exact packet_mem_of_chunk packets001_group packet0044_membership
  · exact packet_mem_of_chunk packets001_group packet0045_membership
  · exact packet_mem_of_chunk packets002_group packet0048_membership
  · exact packet_mem_of_chunk packets002_group packet0049_membership
  · exact packet_mem_of_chunk packets003_group packet0091_membership
  · exact packet_mem_of_chunk packets003_group packet0092_membership
  · exact packet_mem_of_chunk packets003_group packet0095_membership
  · exact packet_mem_of_chunk packets004_group packet0096_membership
  · exact packet_mem_of_chunk packets004_group packet0107_membership
  · exact packet_mem_of_chunk packets004_group packet0108_membership
  · exact packet_mem_of_chunk packets004_group packet0111_membership
  · exact packet_mem_of_chunk packets004_group packet0112_membership
  · exact packet_mem_of_chunk packets008_group packet0212_membership
  · exact packet_mem_of_chunk packets008_group packet0213_membership
  · exact packet_mem_of_chunk packets009_group packet0216_membership
  · exact packet_mem_of_chunk packets009_group packet0217_membership
  · exact packet_mem_of_chunk packets009_group packet0227_membership
  · exact packet_mem_of_chunk packets009_group packet0228_membership
  · exact packet_mem_of_chunk packets009_group packet0230_membership
  · exact packet_mem_of_chunk packets010_group packet0250_membership
  · exact packet_mem_of_chunk packets010_group packet0252_membership
  · exact packet_mem_of_chunk packets010_group packet0255_membership
  · exact packet_mem_of_chunk packets010_group packet0256_membership
  · exact packet_mem_of_chunk packets017_group packet0423_membership
  · exact packet_mem_of_chunk packets017_group packet0424_membership
  · exact packet_mem_of_chunk packets017_group packet0426_membership
  · exact packet_mem_of_chunk packets018_group packet0434_membership
  · exact packet_mem_of_chunk packets018_group packet0436_membership
  · exact packet_mem_of_chunk packets019_group packet0458_membership
  · exact packet_mem_of_chunk packets019_group packet0460_membership
  · exact packet_mem_of_chunk packets019_group packet0464_membership
  · exact packet_mem_of_chunk packets019_group packet0465_membership

def slice005Packets : List StripRowPacket :=
  [packet0034, packet0035, packet0038, packet0039, packet0046, packet0047,
   packet0050, packet0051, packet0093, packet0094, packet0097, packet0098,
   packet0109, packet0110, packet0113, packet0114, packet0214, packet0215,
   packet0218, packet0219, packet0229, packet0231, packet0251, packet0252,
   packet0255, packet0256, packet0423, packet0424, packet0426, packet0434,
   packet0436, packet0458, packet0460, packet0464, packet0465]

def slice005 : GridSlice := closedSliceOfPackets 5 6 slice005Packets

private theorem slice005_checked_local : checkSlice slice005.vertical 64 slice005 = true := by
  decide +kernel

theorem slice005_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice005 = true := by
  apply sliceCheck_of_packets slice005_checked_local
  intro p hp
  simp only [slice005Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets001_group packet0034_membership
  · exact packet_mem_of_chunk packets001_group packet0035_membership
  · exact packet_mem_of_chunk packets001_group packet0038_membership
  · exact packet_mem_of_chunk packets001_group packet0039_membership
  · exact packet_mem_of_chunk packets001_group packet0046_membership
  · exact packet_mem_of_chunk packets001_group packet0047_membership
  · exact packet_mem_of_chunk packets002_group packet0050_membership
  · exact packet_mem_of_chunk packets002_group packet0051_membership
  · exact packet_mem_of_chunk packets003_group packet0093_membership
  · exact packet_mem_of_chunk packets003_group packet0094_membership
  · exact packet_mem_of_chunk packets004_group packet0097_membership
  · exact packet_mem_of_chunk packets004_group packet0098_membership
  · exact packet_mem_of_chunk packets004_group packet0109_membership
  · exact packet_mem_of_chunk packets004_group packet0110_membership
  · exact packet_mem_of_chunk packets004_group packet0113_membership
  · exact packet_mem_of_chunk packets004_group packet0114_membership
  · exact packet_mem_of_chunk packets008_group packet0214_membership
  · exact packet_mem_of_chunk packets008_group packet0215_membership
  · exact packet_mem_of_chunk packets009_group packet0218_membership
  · exact packet_mem_of_chunk packets009_group packet0219_membership
  · exact packet_mem_of_chunk packets009_group packet0229_membership
  · exact packet_mem_of_chunk packets009_group packet0231_membership
  · exact packet_mem_of_chunk packets010_group packet0251_membership
  · exact packet_mem_of_chunk packets010_group packet0252_membership
  · exact packet_mem_of_chunk packets010_group packet0255_membership
  · exact packet_mem_of_chunk packets010_group packet0256_membership
  · exact packet_mem_of_chunk packets017_group packet0423_membership
  · exact packet_mem_of_chunk packets017_group packet0424_membership
  · exact packet_mem_of_chunk packets017_group packet0426_membership
  · exact packet_mem_of_chunk packets018_group packet0434_membership
  · exact packet_mem_of_chunk packets018_group packet0436_membership
  · exact packet_mem_of_chunk packets019_group packet0458_membership
  · exact packet_mem_of_chunk packets019_group packet0460_membership
  · exact packet_mem_of_chunk packets019_group packet0464_membership
  · exact packet_mem_of_chunk packets019_group packet0465_membership

def slice006Packets : List StripRowPacket :=
  [packet0040, packet0042, packet0052, packet0053, packet0055, packet0056,
   packet0099, packet0100, packet0103, packet0104, packet0115, packet0116,
   packet0119, packet0120, packet0220, packet0221, packet0224, packet0225,
   packet0232, packet0234, packet0253, packet0254, packet0257, packet0258,
   packet0425, packet0427, packet0435, packet0437, packet0459, packet0460,
   packet0464, packet0465]

def slice006 : GridSlice := closedSliceOfPackets 6 7 slice006Packets

private theorem slice006_checked_local : checkSlice slice006.vertical 64 slice006 = true := by
  decide +kernel

theorem slice006_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice006 = true := by
  apply sliceCheck_of_packets slice006_checked_local
  intro p hp
  simp only [slice006Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets001_group packet0040_membership
  · exact packet_mem_of_chunk packets001_group packet0042_membership
  · exact packet_mem_of_chunk packets002_group packet0052_membership
  · exact packet_mem_of_chunk packets002_group packet0053_membership
  · exact packet_mem_of_chunk packets002_group packet0055_membership
  · exact packet_mem_of_chunk packets002_group packet0056_membership
  · exact packet_mem_of_chunk packets004_group packet0099_membership
  · exact packet_mem_of_chunk packets004_group packet0100_membership
  · exact packet_mem_of_chunk packets004_group packet0103_membership
  · exact packet_mem_of_chunk packets004_group packet0104_membership
  · exact packet_mem_of_chunk packets004_group packet0115_membership
  · exact packet_mem_of_chunk packets004_group packet0116_membership
  · exact packet_mem_of_chunk packets004_group packet0119_membership
  · exact packet_mem_of_chunk packets005_group packet0120_membership
  · exact packet_mem_of_chunk packets009_group packet0220_membership
  · exact packet_mem_of_chunk packets009_group packet0221_membership
  · exact packet_mem_of_chunk packets009_group packet0224_membership
  · exact packet_mem_of_chunk packets009_group packet0225_membership
  · exact packet_mem_of_chunk packets009_group packet0232_membership
  · exact packet_mem_of_chunk packets009_group packet0234_membership
  · exact packet_mem_of_chunk packets010_group packet0253_membership
  · exact packet_mem_of_chunk packets010_group packet0254_membership
  · exact packet_mem_of_chunk packets010_group packet0257_membership
  · exact packet_mem_of_chunk packets010_group packet0258_membership
  · exact packet_mem_of_chunk packets017_group packet0425_membership
  · exact packet_mem_of_chunk packets017_group packet0427_membership
  · exact packet_mem_of_chunk packets018_group packet0435_membership
  · exact packet_mem_of_chunk packets018_group packet0437_membership
  · exact packet_mem_of_chunk packets019_group packet0459_membership
  · exact packet_mem_of_chunk packets019_group packet0460_membership
  · exact packet_mem_of_chunk packets019_group packet0464_membership
  · exact packet_mem_of_chunk packets019_group packet0465_membership

def slice007Packets : List StripRowPacket :=
  [packet0041, packet0043, packet0054, packet0057, packet0058, packet0101,
   packet0102, packet0105, packet0106, packet0117, packet0118, packet0121,
   packet0122, packet0222, packet0223, packet0226, packet0233, packet0235,
   packet0253, packet0254, packet0257, packet0258, packet0425, packet0427,
   packet0435, packet0437, packet0459, packet0460, packet0464, packet0465]

def slice007 : GridSlice := closedSliceOfPackets 7 8 slice007Packets

private theorem slice007_checked_local : checkSlice slice007.vertical 64 slice007 = true := by
  decide +kernel

theorem slice007_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice007 = true := by
  apply sliceCheck_of_packets slice007_checked_local
  intro p hp
  simp only [slice007Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets001_group packet0041_membership
  · exact packet_mem_of_chunk packets001_group packet0043_membership
  · exact packet_mem_of_chunk packets002_group packet0054_membership
  · exact packet_mem_of_chunk packets002_group packet0057_membership
  · exact packet_mem_of_chunk packets002_group packet0058_membership
  · exact packet_mem_of_chunk packets004_group packet0101_membership
  · exact packet_mem_of_chunk packets004_group packet0102_membership
  · exact packet_mem_of_chunk packets004_group packet0105_membership
  · exact packet_mem_of_chunk packets004_group packet0106_membership
  · exact packet_mem_of_chunk packets004_group packet0117_membership
  · exact packet_mem_of_chunk packets004_group packet0118_membership
  · exact packet_mem_of_chunk packets005_group packet0121_membership
  · exact packet_mem_of_chunk packets005_group packet0122_membership
  · exact packet_mem_of_chunk packets009_group packet0222_membership
  · exact packet_mem_of_chunk packets009_group packet0223_membership
  · exact packet_mem_of_chunk packets009_group packet0226_membership
  · exact packet_mem_of_chunk packets009_group packet0233_membership
  · exact packet_mem_of_chunk packets009_group packet0235_membership
  · exact packet_mem_of_chunk packets010_group packet0253_membership
  · exact packet_mem_of_chunk packets010_group packet0254_membership
  · exact packet_mem_of_chunk packets010_group packet0257_membership
  · exact packet_mem_of_chunk packets010_group packet0258_membership
  · exact packet_mem_of_chunk packets017_group packet0425_membership
  · exact packet_mem_of_chunk packets017_group packet0427_membership
  · exact packet_mem_of_chunk packets018_group packet0435_membership
  · exact packet_mem_of_chunk packets018_group packet0437_membership
  · exact packet_mem_of_chunk packets019_group packet0459_membership
  · exact packet_mem_of_chunk packets019_group packet0460_membership
  · exact packet_mem_of_chunk packets019_group packet0464_membership
  · exact packet_mem_of_chunk packets019_group packet0465_membership


end RKCert.ReviewedNative.ThreeInteriorPencil
