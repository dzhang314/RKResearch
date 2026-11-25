module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorLiteralStripRows

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

def slice032Packets : List StripRowPacket :=
  [packet0585, packet0586, packet0589, packet0591, packet0604, packet0606,
   packet0611, packet0612, packet0651, packet0652, packet0655, packet0656,
   packet0667, packet0668, packet0671]

def slice032 : GridSlice := closedSliceOfPackets 48 50 slice032Packets

private theorem slice032_checked_local : checkSlice slice032.vertical 64 slice032 = true := by
  decide +kernel

theorem slice032_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice032 = true := by
  apply sliceCheck_of_packets slice032_checked_local
  intro p hp
  simp only [slice032Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets024_group packet0585_membership
  · exact packet_mem_of_chunk packets024_group packet0586_membership
  · exact packet_mem_of_chunk packets024_group packet0589_membership
  · exact packet_mem_of_chunk packets024_group packet0591_membership
  · exact packet_mem_of_chunk packets025_group packet0604_membership
  · exact packet_mem_of_chunk packets025_group packet0606_membership
  · exact packet_mem_of_chunk packets025_group packet0611_membership
  · exact packet_mem_of_chunk packets025_group packet0612_membership
  · exact packet_mem_of_chunk packets027_group packet0651_membership
  · exact packet_mem_of_chunk packets027_group packet0652_membership
  · exact packet_mem_of_chunk packets027_group packet0655_membership
  · exact packet_mem_of_chunk packets027_group packet0656_membership
  · exact packet_mem_of_chunk packets027_group packet0667_membership
  · exact packet_mem_of_chunk packets027_group packet0668_membership
  · exact packet_mem_of_chunk packets027_group packet0671_membership

def slice033Packets : List StripRowPacket :=
  [packet0585, packet0586, packet0590, packet0592, packet0605, packet0607,
   packet0611, packet0612, packet0651, packet0652, packet0655, packet0656,
   packet0667, packet0668, packet0671]

def slice033 : GridSlice := closedSliceOfPackets 50 52 slice033Packets

private theorem slice033_checked_local : checkSlice slice033.vertical 64 slice033 = true := by
  decide +kernel

theorem slice033_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice033 = true := by
  apply sliceCheck_of_packets slice033_checked_local
  intro p hp
  simp only [slice033Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets024_group packet0585_membership
  · exact packet_mem_of_chunk packets024_group packet0586_membership
  · exact packet_mem_of_chunk packets024_group packet0590_membership
  · exact packet_mem_of_chunk packets024_group packet0592_membership
  · exact packet_mem_of_chunk packets025_group packet0605_membership
  · exact packet_mem_of_chunk packets025_group packet0607_membership
  · exact packet_mem_of_chunk packets025_group packet0611_membership
  · exact packet_mem_of_chunk packets025_group packet0612_membership
  · exact packet_mem_of_chunk packets027_group packet0651_membership
  · exact packet_mem_of_chunk packets027_group packet0652_membership
  · exact packet_mem_of_chunk packets027_group packet0655_membership
  · exact packet_mem_of_chunk packets027_group packet0656_membership
  · exact packet_mem_of_chunk packets027_group packet0667_membership
  · exact packet_mem_of_chunk packets027_group packet0668_membership
  · exact packet_mem_of_chunk packets027_group packet0671_membership

def slice034Packets : List StripRowPacket :=
  [packet0587, packet0588, packet0593, packet0594, packet0608, packet0610,
   packet0613, packet0614, packet0653, packet0654, packet0657, packet0658,
   packet0669, packet0670, packet0672]

def slice034 : GridSlice := closedSliceOfPackets 52 54 slice034Packets

private theorem slice034_checked_local : checkSlice slice034.vertical 64 slice034 = true := by
  decide +kernel

theorem slice034_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice034 = true := by
  apply sliceCheck_of_packets slice034_checked_local
  intro p hp
  simp only [slice034Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets024_group packet0587_membership
  · exact packet_mem_of_chunk packets024_group packet0588_membership
  · exact packet_mem_of_chunk packets024_group packet0593_membership
  · exact packet_mem_of_chunk packets024_group packet0594_membership
  · exact packet_mem_of_chunk packets025_group packet0608_membership
  · exact packet_mem_of_chunk packets025_group packet0610_membership
  · exact packet_mem_of_chunk packets025_group packet0613_membership
  · exact packet_mem_of_chunk packets025_group packet0614_membership
  · exact packet_mem_of_chunk packets027_group packet0653_membership
  · exact packet_mem_of_chunk packets027_group packet0654_membership
  · exact packet_mem_of_chunk packets027_group packet0657_membership
  · exact packet_mem_of_chunk packets027_group packet0658_membership
  · exact packet_mem_of_chunk packets027_group packet0669_membership
  · exact packet_mem_of_chunk packets027_group packet0670_membership
  · exact packet_mem_of_chunk packets028_group packet0672_membership

def slice035Packets : List StripRowPacket :=
  [packet0587, packet0588, packet0593, packet0595, packet0609, packet0610,
   packet0613, packet0614, packet0653, packet0654, packet0657, packet0658,
   packet0669, packet0670, packet0672]

def slice035 : GridSlice := closedSliceOfPackets 54 56 slice035Packets

private theorem slice035_checked_local : checkSlice slice035.vertical 64 slice035 = true := by
  decide +kernel

theorem slice035_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice035 = true := by
  apply sliceCheck_of_packets slice035_checked_local
  intro p hp
  simp only [slice035Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets024_group packet0587_membership
  · exact packet_mem_of_chunk packets024_group packet0588_membership
  · exact packet_mem_of_chunk packets024_group packet0593_membership
  · exact packet_mem_of_chunk packets024_group packet0595_membership
  · exact packet_mem_of_chunk packets025_group packet0609_membership
  · exact packet_mem_of_chunk packets025_group packet0610_membership
  · exact packet_mem_of_chunk packets025_group packet0613_membership
  · exact packet_mem_of_chunk packets025_group packet0614_membership
  · exact packet_mem_of_chunk packets027_group packet0653_membership
  · exact packet_mem_of_chunk packets027_group packet0654_membership
  · exact packet_mem_of_chunk packets027_group packet0657_membership
  · exact packet_mem_of_chunk packets027_group packet0658_membership
  · exact packet_mem_of_chunk packets027_group packet0669_membership
  · exact packet_mem_of_chunk packets027_group packet0670_membership
  · exact packet_mem_of_chunk packets028_group packet0672_membership

def slice036Packets : List StripRowPacket :=
  [packet0596, packet0597, packet0600, packet0601, packet0615, packet0616,
   packet0619, packet0620, packet0659, packet0660, packet0663, packet0664,
   packet0673, packet0674, packet0677]

def slice036 : GridSlice := closedSliceOfPackets 56 60 slice036Packets

private theorem slice036_checked_local : checkSlice slice036.vertical 64 slice036 = true := by
  decide +kernel

theorem slice036_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice036 = true := by
  apply sliceCheck_of_packets slice036_checked_local
  intro p hp
  simp only [slice036Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets024_group packet0596_membership
  · exact packet_mem_of_chunk packets024_group packet0597_membership
  · exact packet_mem_of_chunk packets025_group packet0600_membership
  · exact packet_mem_of_chunk packets025_group packet0601_membership
  · exact packet_mem_of_chunk packets025_group packet0615_membership
  · exact packet_mem_of_chunk packets025_group packet0616_membership
  · exact packet_mem_of_chunk packets025_group packet0619_membership
  · exact packet_mem_of_chunk packets025_group packet0620_membership
  · exact packet_mem_of_chunk packets027_group packet0659_membership
  · exact packet_mem_of_chunk packets027_group packet0660_membership
  · exact packet_mem_of_chunk packets027_group packet0663_membership
  · exact packet_mem_of_chunk packets027_group packet0664_membership
  · exact packet_mem_of_chunk packets028_group packet0673_membership
  · exact packet_mem_of_chunk packets028_group packet0674_membership
  · exact packet_mem_of_chunk packets028_group packet0677_membership

def slice037Packets : List StripRowPacket :=
  [packet0598, packet0599, packet0602, packet0603, packet0617, packet0618,
   packet0621, packet0622, packet0661, packet0662, packet0665, packet0666,
   packet0675, packet0676, packet0678]

def slice037 : GridSlice := closedSliceOfPackets 60 64 slice037Packets

private theorem slice037_checked_local : checkSlice slice037.vertical 64 slice037 = true := by
  decide +kernel

theorem slice037_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice037 = true := by
  apply sliceCheck_of_packets slice037_checked_local
  intro p hp
  simp only [slice037Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets024_group packet0598_membership
  · exact packet_mem_of_chunk packets024_group packet0599_membership
  · exact packet_mem_of_chunk packets025_group packet0602_membership
  · exact packet_mem_of_chunk packets025_group packet0603_membership
  · exact packet_mem_of_chunk packets025_group packet0617_membership
  · exact packet_mem_of_chunk packets025_group packet0618_membership
  · exact packet_mem_of_chunk packets025_group packet0621_membership
  · exact packet_mem_of_chunk packets025_group packet0622_membership
  · exact packet_mem_of_chunk packets027_group packet0661_membership
  · exact packet_mem_of_chunk packets027_group packet0662_membership
  · exact packet_mem_of_chunk packets027_group packet0665_membership
  · exact packet_mem_of_chunk packets027_group packet0666_membership
  · exact packet_mem_of_chunk packets028_group packet0675_membership
  · exact packet_mem_of_chunk packets028_group packet0676_membership
  · exact packet_mem_of_chunk packets028_group packet0678_membership

def slice038Packets : List StripRowPacket :=
  [packet0679, packet0680, packet0683, packet0684, packet0691, packet0692,
   packet0695, packet0696, packet0719, packet0720, packet0723, packet0724,
   packet0735, packet0736, packet0739]

def slice038 : GridSlice := closedSliceOfPackets 64 68 slice038Packets

private theorem slice038_checked_local : checkSlice slice038.vertical 64 slice038 = true := by
  decide +kernel

theorem slice038_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice038 = true := by
  apply sliceCheck_of_packets slice038_checked_local
  intro p hp
  simp only [slice038Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets028_group packet0679_membership
  · exact packet_mem_of_chunk packets028_group packet0680_membership
  · exact packet_mem_of_chunk packets028_group packet0683_membership
  · exact packet_mem_of_chunk packets028_group packet0684_membership
  · exact packet_mem_of_chunk packets028_group packet0691_membership
  · exact packet_mem_of_chunk packets028_group packet0692_membership
  · exact packet_mem_of_chunk packets028_group packet0695_membership
  · exact packet_mem_of_chunk packets029_group packet0696_membership
  · exact packet_mem_of_chunk packets029_group packet0719_membership
  · exact packet_mem_of_chunk packets030_group packet0720_membership
  · exact packet_mem_of_chunk packets030_group packet0723_membership
  · exact packet_mem_of_chunk packets030_group packet0724_membership
  · exact packet_mem_of_chunk packets030_group packet0735_membership
  · exact packet_mem_of_chunk packets030_group packet0736_membership
  · exact packet_mem_of_chunk packets030_group packet0739_membership

def slice039Packets : List StripRowPacket :=
  [packet0681, packet0682, packet0685, packet0686, packet0693, packet0694,
   packet0697, packet0698, packet0721, packet0722, packet0725, packet0726,
   packet0737, packet0738, packet0740]

def slice039 : GridSlice := closedSliceOfPackets 68 72 slice039Packets

private theorem slice039_checked_local : checkSlice slice039.vertical 64 slice039 = true := by
  decide +kernel

theorem slice039_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice039 = true := by
  apply sliceCheck_of_packets slice039_checked_local
  intro p hp
  simp only [slice039Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets028_group packet0681_membership
  · exact packet_mem_of_chunk packets028_group packet0682_membership
  · exact packet_mem_of_chunk packets028_group packet0685_membership
  · exact packet_mem_of_chunk packets028_group packet0686_membership
  · exact packet_mem_of_chunk packets028_group packet0693_membership
  · exact packet_mem_of_chunk packets028_group packet0694_membership
  · exact packet_mem_of_chunk packets029_group packet0697_membership
  · exact packet_mem_of_chunk packets029_group packet0698_membership
  · exact packet_mem_of_chunk packets030_group packet0721_membership
  · exact packet_mem_of_chunk packets030_group packet0722_membership
  · exact packet_mem_of_chunk packets030_group packet0725_membership
  · exact packet_mem_of_chunk packets030_group packet0726_membership
  · exact packet_mem_of_chunk packets030_group packet0737_membership
  · exact packet_mem_of_chunk packets030_group packet0738_membership
  · exact packet_mem_of_chunk packets030_group packet0740_membership


end RKCert.ReviewedNative.ThreeInteriorPencil
