module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorLiteralStripRows

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

def slice024Packets : List StripRowPacket :=
  [packet0502, packet0504, packet0505, packet0513, packet0514, packet0517,
   packet0518, packet0548, packet0549, packet0552, packet0553, packet0564,
   packet0566, packet0623, packet0624, packet0627, packet0628, packet0639,
   packet0640, packet0643]

def slice024 : GridSlice := closedSliceOfPackets 32 34 slice024Packets

private theorem slice024_checked_local : checkSlice slice024.vertical 64 slice024 = true := by
  decide +kernel

theorem slice024_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice024 = true := by
  apply sliceCheck_of_packets slice024_checked_local
  intro p hp
  simp only [slice024Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets020_group packet0502_membership
  · exact packet_mem_of_chunk packets021_group packet0504_membership
  · exact packet_mem_of_chunk packets021_group packet0505_membership
  · exact packet_mem_of_chunk packets021_group packet0513_membership
  · exact packet_mem_of_chunk packets021_group packet0514_membership
  · exact packet_mem_of_chunk packets021_group packet0517_membership
  · exact packet_mem_of_chunk packets021_group packet0518_membership
  · exact packet_mem_of_chunk packets022_group packet0548_membership
  · exact packet_mem_of_chunk packets022_group packet0549_membership
  · exact packet_mem_of_chunk packets023_group packet0552_membership
  · exact packet_mem_of_chunk packets023_group packet0553_membership
  · exact packet_mem_of_chunk packets023_group packet0564_membership
  · exact packet_mem_of_chunk packets023_group packet0566_membership
  · exact packet_mem_of_chunk packets025_group packet0623_membership
  · exact packet_mem_of_chunk packets026_group packet0624_membership
  · exact packet_mem_of_chunk packets026_group packet0627_membership
  · exact packet_mem_of_chunk packets026_group packet0628_membership
  · exact packet_mem_of_chunk packets026_group packet0639_membership
  · exact packet_mem_of_chunk packets026_group packet0640_membership
  · exact packet_mem_of_chunk packets026_group packet0643_membership

def slice025Packets : List StripRowPacket :=
  [packet0503, packet0506, packet0507, packet0515, packet0516, packet0519,
   packet0520, packet0550, packet0551, packet0554, packet0555, packet0565,
   packet0566, packet0623, packet0624, packet0627, packet0628, packet0639,
   packet0640, packet0643]

def slice025 : GridSlice := closedSliceOfPackets 34 36 slice025Packets

private theorem slice025_checked_local : checkSlice slice025.vertical 64 slice025 = true := by
  decide +kernel

theorem slice025_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice025 = true := by
  apply sliceCheck_of_packets slice025_checked_local
  intro p hp
  simp only [slice025Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets020_group packet0503_membership
  · exact packet_mem_of_chunk packets021_group packet0506_membership
  · exact packet_mem_of_chunk packets021_group packet0507_membership
  · exact packet_mem_of_chunk packets021_group packet0515_membership
  · exact packet_mem_of_chunk packets021_group packet0516_membership
  · exact packet_mem_of_chunk packets021_group packet0519_membership
  · exact packet_mem_of_chunk packets021_group packet0520_membership
  · exact packet_mem_of_chunk packets022_group packet0550_membership
  · exact packet_mem_of_chunk packets022_group packet0551_membership
  · exact packet_mem_of_chunk packets023_group packet0554_membership
  · exact packet_mem_of_chunk packets023_group packet0555_membership
  · exact packet_mem_of_chunk packets023_group packet0565_membership
  · exact packet_mem_of_chunk packets023_group packet0566_membership
  · exact packet_mem_of_chunk packets025_group packet0623_membership
  · exact packet_mem_of_chunk packets026_group packet0624_membership
  · exact packet_mem_of_chunk packets026_group packet0627_membership
  · exact packet_mem_of_chunk packets026_group packet0628_membership
  · exact packet_mem_of_chunk packets026_group packet0639_membership
  · exact packet_mem_of_chunk packets026_group packet0640_membership
  · exact packet_mem_of_chunk packets026_group packet0643_membership

def slice026Packets : List StripRowPacket :=
  [packet0508, packet0510, packet0511, packet0521, packet0522, packet0525,
   packet0526, packet0556, packet0557, packet0560, packet0561, packet0567,
   packet0569, packet0625, packet0626, packet0629, packet0630, packet0641,
   packet0642, packet0644]

def slice026 : GridSlice := closedSliceOfPackets 36 38 slice026Packets

private theorem slice026_checked_local : checkSlice slice026.vertical 64 slice026 = true := by
  decide +kernel

theorem slice026_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice026 = true := by
  apply sliceCheck_of_packets slice026_checked_local
  intro p hp
  simp only [slice026Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets021_group packet0508_membership
  · exact packet_mem_of_chunk packets021_group packet0510_membership
  · exact packet_mem_of_chunk packets021_group packet0511_membership
  · exact packet_mem_of_chunk packets021_group packet0521_membership
  · exact packet_mem_of_chunk packets021_group packet0522_membership
  · exact packet_mem_of_chunk packets021_group packet0525_membership
  · exact packet_mem_of_chunk packets021_group packet0526_membership
  · exact packet_mem_of_chunk packets023_group packet0556_membership
  · exact packet_mem_of_chunk packets023_group packet0557_membership
  · exact packet_mem_of_chunk packets023_group packet0560_membership
  · exact packet_mem_of_chunk packets023_group packet0561_membership
  · exact packet_mem_of_chunk packets023_group packet0567_membership
  · exact packet_mem_of_chunk packets023_group packet0569_membership
  · exact packet_mem_of_chunk packets026_group packet0625_membership
  · exact packet_mem_of_chunk packets026_group packet0626_membership
  · exact packet_mem_of_chunk packets026_group packet0629_membership
  · exact packet_mem_of_chunk packets026_group packet0630_membership
  · exact packet_mem_of_chunk packets026_group packet0641_membership
  · exact packet_mem_of_chunk packets026_group packet0642_membership
  · exact packet_mem_of_chunk packets026_group packet0644_membership

def slice027Packets : List StripRowPacket :=
  [packet0509, packet0512, packet0523, packet0524, packet0527, packet0528,
   packet0558, packet0559, packet0562, packet0563, packet0568, packet0569,
   packet0625, packet0626, packet0629, packet0630, packet0641, packet0642,
   packet0644]

def slice027 : GridSlice := closedSliceOfPackets 38 40 slice027Packets

private theorem slice027_checked_local : checkSlice slice027.vertical 64 slice027 = true := by
  decide +kernel

theorem slice027_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice027 = true := by
  apply sliceCheck_of_packets slice027_checked_local
  intro p hp
  simp only [slice027Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets021_group packet0509_membership
  · exact packet_mem_of_chunk packets021_group packet0512_membership
  · exact packet_mem_of_chunk packets021_group packet0523_membership
  · exact packet_mem_of_chunk packets021_group packet0524_membership
  · exact packet_mem_of_chunk packets021_group packet0527_membership
  · exact packet_mem_of_chunk packets022_group packet0528_membership
  · exact packet_mem_of_chunk packets023_group packet0558_membership
  · exact packet_mem_of_chunk packets023_group packet0559_membership
  · exact packet_mem_of_chunk packets023_group packet0562_membership
  · exact packet_mem_of_chunk packets023_group packet0563_membership
  · exact packet_mem_of_chunk packets023_group packet0568_membership
  · exact packet_mem_of_chunk packets023_group packet0569_membership
  · exact packet_mem_of_chunk packets026_group packet0625_membership
  · exact packet_mem_of_chunk packets026_group packet0626_membership
  · exact packet_mem_of_chunk packets026_group packet0629_membership
  · exact packet_mem_of_chunk packets026_group packet0630_membership
  · exact packet_mem_of_chunk packets026_group packet0641_membership
  · exact packet_mem_of_chunk packets026_group packet0642_membership
  · exact packet_mem_of_chunk packets026_group packet0644_membership

def slice028Packets : List StripRowPacket :=
  [packet0529, packet0530, packet0534, packet0535, packet0538, packet0539,
   packet0570, packet0571, packet0574, packet0581, packet0582, packet0631,
   packet0632, packet0635, packet0636, packet0645, packet0646, packet0649]

def slice028 : GridSlice := closedSliceOfPackets 40 42 slice028Packets

private theorem slice028_checked_local : checkSlice slice028.vertical 64 slice028 = true := by
  decide +kernel

theorem slice028_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice028 = true := by
  apply sliceCheck_of_packets slice028_checked_local
  intro p hp
  simp only [slice028Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets022_group packet0529_membership
  · exact packet_mem_of_chunk packets022_group packet0530_membership
  · exact packet_mem_of_chunk packets022_group packet0534_membership
  · exact packet_mem_of_chunk packets022_group packet0535_membership
  · exact packet_mem_of_chunk packets022_group packet0538_membership
  · exact packet_mem_of_chunk packets022_group packet0539_membership
  · exact packet_mem_of_chunk packets023_group packet0570_membership
  · exact packet_mem_of_chunk packets023_group packet0571_membership
  · exact packet_mem_of_chunk packets023_group packet0574_membership
  · exact packet_mem_of_chunk packets024_group packet0581_membership
  · exact packet_mem_of_chunk packets024_group packet0582_membership
  · exact packet_mem_of_chunk packets026_group packet0631_membership
  · exact packet_mem_of_chunk packets026_group packet0632_membership
  · exact packet_mem_of_chunk packets026_group packet0635_membership
  · exact packet_mem_of_chunk packets026_group packet0636_membership
  · exact packet_mem_of_chunk packets026_group packet0645_membership
  · exact packet_mem_of_chunk packets026_group packet0646_membership
  · exact packet_mem_of_chunk packets027_group packet0649_membership

def slice029Packets : List StripRowPacket :=
  [packet0529, packet0531, packet0536, packet0537, packet0540, packet0541,
   packet0572, packet0573, packet0575, packet0581, packet0582, packet0631,
   packet0632, packet0635, packet0636, packet0645, packet0646, packet0649]

def slice029 : GridSlice := closedSliceOfPackets 42 44 slice029Packets

private theorem slice029_checked_local : checkSlice slice029.vertical 64 slice029 = true := by
  decide +kernel

theorem slice029_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice029 = true := by
  apply sliceCheck_of_packets slice029_checked_local
  intro p hp
  simp only [slice029Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets022_group packet0529_membership
  · exact packet_mem_of_chunk packets022_group packet0531_membership
  · exact packet_mem_of_chunk packets022_group packet0536_membership
  · exact packet_mem_of_chunk packets022_group packet0537_membership
  · exact packet_mem_of_chunk packets022_group packet0540_membership
  · exact packet_mem_of_chunk packets022_group packet0541_membership
  · exact packet_mem_of_chunk packets023_group packet0572_membership
  · exact packet_mem_of_chunk packets023_group packet0573_membership
  · exact packet_mem_of_chunk packets023_group packet0575_membership
  · exact packet_mem_of_chunk packets024_group packet0581_membership
  · exact packet_mem_of_chunk packets024_group packet0582_membership
  · exact packet_mem_of_chunk packets026_group packet0631_membership
  · exact packet_mem_of_chunk packets026_group packet0632_membership
  · exact packet_mem_of_chunk packets026_group packet0635_membership
  · exact packet_mem_of_chunk packets026_group packet0636_membership
  · exact packet_mem_of_chunk packets026_group packet0645_membership
  · exact packet_mem_of_chunk packets026_group packet0646_membership
  · exact packet_mem_of_chunk packets027_group packet0649_membership

def slice030Packets : List StripRowPacket :=
  [packet0532, packet0533, packet0542, packet0544, packet0545, packet0576,
   packet0577, packet0579, packet0583, packet0584, packet0633, packet0634,
   packet0637, packet0638, packet0647, packet0648, packet0650]

def slice030 : GridSlice := closedSliceOfPackets 44 46 slice030Packets

private theorem slice030_checked_local : checkSlice slice030.vertical 64 slice030 = true := by
  decide +kernel

theorem slice030_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice030 = true := by
  apply sliceCheck_of_packets slice030_checked_local
  intro p hp
  simp only [slice030Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets022_group packet0532_membership
  · exact packet_mem_of_chunk packets022_group packet0533_membership
  · exact packet_mem_of_chunk packets022_group packet0542_membership
  · exact packet_mem_of_chunk packets022_group packet0544_membership
  · exact packet_mem_of_chunk packets022_group packet0545_membership
  · exact packet_mem_of_chunk packets024_group packet0576_membership
  · exact packet_mem_of_chunk packets024_group packet0577_membership
  · exact packet_mem_of_chunk packets024_group packet0579_membership
  · exact packet_mem_of_chunk packets024_group packet0583_membership
  · exact packet_mem_of_chunk packets024_group packet0584_membership
  · exact packet_mem_of_chunk packets026_group packet0633_membership
  · exact packet_mem_of_chunk packets026_group packet0634_membership
  · exact packet_mem_of_chunk packets026_group packet0637_membership
  · exact packet_mem_of_chunk packets026_group packet0638_membership
  · exact packet_mem_of_chunk packets026_group packet0647_membership
  · exact packet_mem_of_chunk packets027_group packet0648_membership
  · exact packet_mem_of_chunk packets027_group packet0650_membership

def slice031Packets : List StripRowPacket :=
  [packet0532, packet0533, packet0543, packet0546, packet0547, packet0578,
   packet0580, packet0583, packet0584, packet0633, packet0634, packet0637,
   packet0638, packet0647, packet0648, packet0650]

def slice031 : GridSlice := closedSliceOfPackets 46 48 slice031Packets

private theorem slice031_checked_local : checkSlice slice031.vertical 64 slice031 = true := by
  decide +kernel

theorem slice031_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice031 = true := by
  apply sliceCheck_of_packets slice031_checked_local
  intro p hp
  simp only [slice031Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets022_group packet0532_membership
  · exact packet_mem_of_chunk packets022_group packet0533_membership
  · exact packet_mem_of_chunk packets022_group packet0543_membership
  · exact packet_mem_of_chunk packets022_group packet0546_membership
  · exact packet_mem_of_chunk packets022_group packet0547_membership
  · exact packet_mem_of_chunk packets024_group packet0578_membership
  · exact packet_mem_of_chunk packets024_group packet0580_membership
  · exact packet_mem_of_chunk packets024_group packet0583_membership
  · exact packet_mem_of_chunk packets024_group packet0584_membership
  · exact packet_mem_of_chunk packets026_group packet0633_membership
  · exact packet_mem_of_chunk packets026_group packet0634_membership
  · exact packet_mem_of_chunk packets026_group packet0637_membership
  · exact packet_mem_of_chunk packets026_group packet0638_membership
  · exact packet_mem_of_chunk packets026_group packet0647_membership
  · exact packet_mem_of_chunk packets027_group packet0648_membership
  · exact packet_mem_of_chunk packets027_group packet0650_membership


end RKCert.ReviewedNative.ThreeInteriorPencil
