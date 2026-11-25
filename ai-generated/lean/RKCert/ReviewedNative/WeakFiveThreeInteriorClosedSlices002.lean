module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorLiteralStripRows

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

def slice016Packets : List StripRowPacket :=
  [packet0300, packet0301, packet0304, packet0305, packet0316, packet0317,
   packet0320, packet0321, packet0363, packet0364, packet0367, packet0368,
   packet0379, packet0380, packet0383, packet0473, packet0474, packet0477,
   packet0479, packet0490, packet0491, packet0494]

def slice016 : GridSlice := closedSliceOfPackets 16 18 slice016Packets

private theorem slice016_checked_local : checkSlice slice016.vertical 64 slice016 = true := by
  decide +kernel

theorem slice016_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice016 = true := by
  apply sliceCheck_of_packets slice016_checked_local
  intro p hp
  simp only [slice016Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets012_group packet0300_membership
  · exact packet_mem_of_chunk packets012_group packet0301_membership
  · exact packet_mem_of_chunk packets012_group packet0304_membership
  · exact packet_mem_of_chunk packets012_group packet0305_membership
  · exact packet_mem_of_chunk packets013_group packet0316_membership
  · exact packet_mem_of_chunk packets013_group packet0317_membership
  · exact packet_mem_of_chunk packets013_group packet0320_membership
  · exact packet_mem_of_chunk packets013_group packet0321_membership
  · exact packet_mem_of_chunk packets015_group packet0363_membership
  · exact packet_mem_of_chunk packets015_group packet0364_membership
  · exact packet_mem_of_chunk packets015_group packet0367_membership
  · exact packet_mem_of_chunk packets015_group packet0368_membership
  · exact packet_mem_of_chunk packets015_group packet0379_membership
  · exact packet_mem_of_chunk packets015_group packet0380_membership
  · exact packet_mem_of_chunk packets015_group packet0383_membership
  · exact packet_mem_of_chunk packets019_group packet0473_membership
  · exact packet_mem_of_chunk packets019_group packet0474_membership
  · exact packet_mem_of_chunk packets019_group packet0477_membership
  · exact packet_mem_of_chunk packets019_group packet0479_membership
  · exact packet_mem_of_chunk packets020_group packet0490_membership
  · exact packet_mem_of_chunk packets020_group packet0491_membership
  · exact packet_mem_of_chunk packets020_group packet0494_membership

def slice017Packets : List StripRowPacket :=
  [packet0302, packet0303, packet0306, packet0307, packet0318, packet0319,
   packet0322, packet0323, packet0365, packet0366, packet0369, packet0370,
   packet0381, packet0382, packet0384, packet0473, packet0474, packet0478,
   packet0479, packet0490, packet0491, packet0494]

def slice017 : GridSlice := closedSliceOfPackets 18 20 slice017Packets

private theorem slice017_checked_local : checkSlice slice017.vertical 64 slice017 = true := by
  decide +kernel

theorem slice017_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice017 = true := by
  apply sliceCheck_of_packets slice017_checked_local
  intro p hp
  simp only [slice017Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets012_group packet0302_membership
  · exact packet_mem_of_chunk packets012_group packet0303_membership
  · exact packet_mem_of_chunk packets012_group packet0306_membership
  · exact packet_mem_of_chunk packets012_group packet0307_membership
  · exact packet_mem_of_chunk packets013_group packet0318_membership
  · exact packet_mem_of_chunk packets013_group packet0319_membership
  · exact packet_mem_of_chunk packets013_group packet0322_membership
  · exact packet_mem_of_chunk packets013_group packet0323_membership
  · exact packet_mem_of_chunk packets015_group packet0365_membership
  · exact packet_mem_of_chunk packets015_group packet0366_membership
  · exact packet_mem_of_chunk packets015_group packet0369_membership
  · exact packet_mem_of_chunk packets015_group packet0370_membership
  · exact packet_mem_of_chunk packets015_group packet0381_membership
  · exact packet_mem_of_chunk packets015_group packet0382_membership
  · exact packet_mem_of_chunk packets016_group packet0384_membership
  · exact packet_mem_of_chunk packets019_group packet0473_membership
  · exact packet_mem_of_chunk packets019_group packet0474_membership
  · exact packet_mem_of_chunk packets019_group packet0478_membership
  · exact packet_mem_of_chunk packets019_group packet0479_membership
  · exact packet_mem_of_chunk packets020_group packet0490_membership
  · exact packet_mem_of_chunk packets020_group packet0491_membership
  · exact packet_mem_of_chunk packets020_group packet0494_membership

def slice018Packets : List StripRowPacket :=
  [packet0308, packet0309, packet0312, packet0313, packet0324, packet0325,
   packet0328, packet0329, packet0371, packet0372, packet0375, packet0376,
   packet0385, packet0386, packet0389, packet0475, packet0476, packet0480,
   packet0481, packet0492, packet0493, packet0495]

def slice018 : GridSlice := closedSliceOfPackets 20 22 slice018Packets

private theorem slice018_checked_local : checkSlice slice018.vertical 64 slice018 = true := by
  decide +kernel

theorem slice018_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice018 = true := by
  apply sliceCheck_of_packets slice018_checked_local
  intro p hp
  simp only [slice018Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets012_group packet0308_membership
  · exact packet_mem_of_chunk packets012_group packet0309_membership
  · exact packet_mem_of_chunk packets013_group packet0312_membership
  · exact packet_mem_of_chunk packets013_group packet0313_membership
  · exact packet_mem_of_chunk packets013_group packet0324_membership
  · exact packet_mem_of_chunk packets013_group packet0325_membership
  · exact packet_mem_of_chunk packets013_group packet0328_membership
  · exact packet_mem_of_chunk packets013_group packet0329_membership
  · exact packet_mem_of_chunk packets015_group packet0371_membership
  · exact packet_mem_of_chunk packets015_group packet0372_membership
  · exact packet_mem_of_chunk packets015_group packet0375_membership
  · exact packet_mem_of_chunk packets015_group packet0376_membership
  · exact packet_mem_of_chunk packets016_group packet0385_membership
  · exact packet_mem_of_chunk packets016_group packet0386_membership
  · exact packet_mem_of_chunk packets016_group packet0389_membership
  · exact packet_mem_of_chunk packets019_group packet0475_membership
  · exact packet_mem_of_chunk packets019_group packet0476_membership
  · exact packet_mem_of_chunk packets020_group packet0480_membership
  · exact packet_mem_of_chunk packets020_group packet0481_membership
  · exact packet_mem_of_chunk packets020_group packet0492_membership
  · exact packet_mem_of_chunk packets020_group packet0493_membership
  · exact packet_mem_of_chunk packets020_group packet0495_membership

def slice019Packets : List StripRowPacket :=
  [packet0310, packet0311, packet0314, packet0315, packet0326, packet0327,
   packet0330, packet0331, packet0373, packet0374, packet0377, packet0378,
   packet0387, packet0388, packet0390, packet0475, packet0476, packet0480,
   packet0481, packet0492, packet0493, packet0495]

def slice019 : GridSlice := closedSliceOfPackets 22 24 slice019Packets

private theorem slice019_checked_local : checkSlice slice019.vertical 64 slice019 = true := by
  decide +kernel

theorem slice019_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice019 = true := by
  apply sliceCheck_of_packets slice019_checked_local
  intro p hp
  simp only [slice019Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets012_group packet0310_membership
  · exact packet_mem_of_chunk packets012_group packet0311_membership
  · exact packet_mem_of_chunk packets013_group packet0314_membership
  · exact packet_mem_of_chunk packets013_group packet0315_membership
  · exact packet_mem_of_chunk packets013_group packet0326_membership
  · exact packet_mem_of_chunk packets013_group packet0327_membership
  · exact packet_mem_of_chunk packets013_group packet0330_membership
  · exact packet_mem_of_chunk packets013_group packet0331_membership
  · exact packet_mem_of_chunk packets015_group packet0373_membership
  · exact packet_mem_of_chunk packets015_group packet0374_membership
  · exact packet_mem_of_chunk packets015_group packet0377_membership
  · exact packet_mem_of_chunk packets015_group packet0378_membership
  · exact packet_mem_of_chunk packets016_group packet0387_membership
  · exact packet_mem_of_chunk packets016_group packet0388_membership
  · exact packet_mem_of_chunk packets016_group packet0390_membership
  · exact packet_mem_of_chunk packets019_group packet0475_membership
  · exact packet_mem_of_chunk packets019_group packet0476_membership
  · exact packet_mem_of_chunk packets020_group packet0480_membership
  · exact packet_mem_of_chunk packets020_group packet0481_membership
  · exact packet_mem_of_chunk packets020_group packet0492_membership
  · exact packet_mem_of_chunk packets020_group packet0493_membership
  · exact packet_mem_of_chunk packets020_group packet0495_membership

def slice020Packets : List StripRowPacket :=
  [packet0332, packet0333, packet0336, packet0337, packet0347, packet0348,
   packet0351, packet0352, packet0391, packet0392, packet0395, packet0396,
   packet0407, packet0408, packet0411, packet0482, packet0483, packet0486,
   packet0487, packet0496, packet0497, packet0500]

def slice020 : GridSlice := closedSliceOfPackets 24 26 slice020Packets

private theorem slice020_checked_local : checkSlice slice020.vertical 64 slice020 = true := by
  decide +kernel

theorem slice020_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice020 = true := by
  apply sliceCheck_of_packets slice020_checked_local
  intro p hp
  simp only [slice020Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets013_group packet0332_membership
  · exact packet_mem_of_chunk packets013_group packet0333_membership
  · exact packet_mem_of_chunk packets014_group packet0336_membership
  · exact packet_mem_of_chunk packets014_group packet0337_membership
  · exact packet_mem_of_chunk packets014_group packet0347_membership
  · exact packet_mem_of_chunk packets014_group packet0348_membership
  · exact packet_mem_of_chunk packets014_group packet0351_membership
  · exact packet_mem_of_chunk packets014_group packet0352_membership
  · exact packet_mem_of_chunk packets016_group packet0391_membership
  · exact packet_mem_of_chunk packets016_group packet0392_membership
  · exact packet_mem_of_chunk packets016_group packet0395_membership
  · exact packet_mem_of_chunk packets016_group packet0396_membership
  · exact packet_mem_of_chunk packets016_group packet0407_membership
  · exact packet_mem_of_chunk packets017_group packet0408_membership
  · exact packet_mem_of_chunk packets017_group packet0411_membership
  · exact packet_mem_of_chunk packets020_group packet0482_membership
  · exact packet_mem_of_chunk packets020_group packet0483_membership
  · exact packet_mem_of_chunk packets020_group packet0486_membership
  · exact packet_mem_of_chunk packets020_group packet0487_membership
  · exact packet_mem_of_chunk packets020_group packet0496_membership
  · exact packet_mem_of_chunk packets020_group packet0497_membership
  · exact packet_mem_of_chunk packets020_group packet0500_membership

def slice021Packets : List StripRowPacket :=
  [packet0334, packet0335, packet0338, packet0339, packet0349, packet0350,
   packet0353, packet0354, packet0393, packet0394, packet0397, packet0398,
   packet0409, packet0410, packet0412, packet0482, packet0483, packet0486,
   packet0487, packet0496, packet0497, packet0500]

def slice021 : GridSlice := closedSliceOfPackets 26 28 slice021Packets

private theorem slice021_checked_local : checkSlice slice021.vertical 64 slice021 = true := by
  decide +kernel

theorem slice021_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice021 = true := by
  apply sliceCheck_of_packets slice021_checked_local
  intro p hp
  simp only [slice021Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets013_group packet0334_membership
  · exact packet_mem_of_chunk packets013_group packet0335_membership
  · exact packet_mem_of_chunk packets014_group packet0338_membership
  · exact packet_mem_of_chunk packets014_group packet0339_membership
  · exact packet_mem_of_chunk packets014_group packet0349_membership
  · exact packet_mem_of_chunk packets014_group packet0350_membership
  · exact packet_mem_of_chunk packets014_group packet0353_membership
  · exact packet_mem_of_chunk packets014_group packet0354_membership
  · exact packet_mem_of_chunk packets016_group packet0393_membership
  · exact packet_mem_of_chunk packets016_group packet0394_membership
  · exact packet_mem_of_chunk packets016_group packet0397_membership
  · exact packet_mem_of_chunk packets016_group packet0398_membership
  · exact packet_mem_of_chunk packets017_group packet0409_membership
  · exact packet_mem_of_chunk packets017_group packet0410_membership
  · exact packet_mem_of_chunk packets017_group packet0412_membership
  · exact packet_mem_of_chunk packets020_group packet0482_membership
  · exact packet_mem_of_chunk packets020_group packet0483_membership
  · exact packet_mem_of_chunk packets020_group packet0486_membership
  · exact packet_mem_of_chunk packets020_group packet0487_membership
  · exact packet_mem_of_chunk packets020_group packet0496_membership
  · exact packet_mem_of_chunk packets020_group packet0497_membership
  · exact packet_mem_of_chunk packets020_group packet0500_membership

def slice022Packets : List StripRowPacket :=
  [packet0340, packet0341, packet0343, packet0344, packet0355, packet0356,
   packet0359, packet0360, packet0399, packet0400, packet0403, packet0404,
   packet0413, packet0415, packet0484, packet0485, packet0488, packet0489,
   packet0498, packet0499, packet0501]

def slice022 : GridSlice := closedSliceOfPackets 28 30 slice022Packets

private theorem slice022_checked_local : checkSlice slice022.vertical 64 slice022 = true := by
  decide +kernel

theorem slice022_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice022 = true := by
  apply sliceCheck_of_packets slice022_checked_local
  intro p hp
  simp only [slice022Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets014_group packet0340_membership
  · exact packet_mem_of_chunk packets014_group packet0341_membership
  · exact packet_mem_of_chunk packets014_group packet0343_membership
  · exact packet_mem_of_chunk packets014_group packet0344_membership
  · exact packet_mem_of_chunk packets014_group packet0355_membership
  · exact packet_mem_of_chunk packets014_group packet0356_membership
  · exact packet_mem_of_chunk packets014_group packet0359_membership
  · exact packet_mem_of_chunk packets015_group packet0360_membership
  · exact packet_mem_of_chunk packets016_group packet0399_membership
  · exact packet_mem_of_chunk packets016_group packet0400_membership
  · exact packet_mem_of_chunk packets016_group packet0403_membership
  · exact packet_mem_of_chunk packets016_group packet0404_membership
  · exact packet_mem_of_chunk packets017_group packet0413_membership
  · exact packet_mem_of_chunk packets017_group packet0415_membership
  · exact packet_mem_of_chunk packets020_group packet0484_membership
  · exact packet_mem_of_chunk packets020_group packet0485_membership
  · exact packet_mem_of_chunk packets020_group packet0488_membership
  · exact packet_mem_of_chunk packets020_group packet0489_membership
  · exact packet_mem_of_chunk packets020_group packet0498_membership
  · exact packet_mem_of_chunk packets020_group packet0499_membership
  · exact packet_mem_of_chunk packets020_group packet0501_membership

def slice023Packets : List StripRowPacket :=
  [packet0342, packet0345, packet0346, packet0357, packet0358, packet0361,
   packet0362, packet0401, packet0402, packet0405, packet0406, packet0414,
   packet0415, packet0484, packet0485, packet0488, packet0489, packet0498,
   packet0499, packet0501]

def slice023 : GridSlice := closedSliceOfPackets 30 32 slice023Packets

private theorem slice023_checked_local : checkSlice slice023.vertical 64 slice023 = true := by
  decide +kernel

theorem slice023_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice023 = true := by
  apply sliceCheck_of_packets slice023_checked_local
  intro p hp
  simp only [slice023Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets014_group packet0342_membership
  · exact packet_mem_of_chunk packets014_group packet0345_membership
  · exact packet_mem_of_chunk packets014_group packet0346_membership
  · exact packet_mem_of_chunk packets014_group packet0357_membership
  · exact packet_mem_of_chunk packets014_group packet0358_membership
  · exact packet_mem_of_chunk packets015_group packet0361_membership
  · exact packet_mem_of_chunk packets015_group packet0362_membership
  · exact packet_mem_of_chunk packets016_group packet0401_membership
  · exact packet_mem_of_chunk packets016_group packet0402_membership
  · exact packet_mem_of_chunk packets016_group packet0405_membership
  · exact packet_mem_of_chunk packets016_group packet0406_membership
  · exact packet_mem_of_chunk packets017_group packet0414_membership
  · exact packet_mem_of_chunk packets017_group packet0415_membership
  · exact packet_mem_of_chunk packets020_group packet0484_membership
  · exact packet_mem_of_chunk packets020_group packet0485_membership
  · exact packet_mem_of_chunk packets020_group packet0488_membership
  · exact packet_mem_of_chunk packets020_group packet0489_membership
  · exact packet_mem_of_chunk packets020_group packet0498_membership
  · exact packet_mem_of_chunk packets020_group packet0499_membership
  · exact packet_mem_of_chunk packets020_group packet0501_membership


end RKCert.ReviewedNative.ThreeInteriorPencil
