module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorLiteralStripRows

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

def slice040Packets : List StripRowPacket :=
  [packet0687, packet0688, packet0689, packet0690, packet0699, packet0700,
   packet0701, packet0702, packet0727, packet0729, packet0731, packet0733,
   packet0741, packet0742, packet0743, packet0744]

def slice040 : GridSlice := closedSliceOfPackets 72 76 slice040Packets

private theorem slice040_checked_local : checkSlice slice040.vertical 64 slice040 = true := by
  decide +kernel

theorem slice040_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice040 = true := by
  apply sliceCheck_of_packets slice040_checked_local
  intro p hp
  simp only [slice040Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets028_group packet0687_membership
  · exact packet_mem_of_chunk packets028_group packet0688_membership
  · exact packet_mem_of_chunk packets028_group packet0689_membership
  · exact packet_mem_of_chunk packets028_group packet0690_membership
  · exact packet_mem_of_chunk packets029_group packet0699_membership
  · exact packet_mem_of_chunk packets029_group packet0700_membership
  · exact packet_mem_of_chunk packets029_group packet0701_membership
  · exact packet_mem_of_chunk packets029_group packet0702_membership
  · exact packet_mem_of_chunk packets030_group packet0727_membership
  · exact packet_mem_of_chunk packets030_group packet0729_membership
  · exact packet_mem_of_chunk packets030_group packet0731_membership
  · exact packet_mem_of_chunk packets030_group packet0733_membership
  · exact packet_mem_of_chunk packets030_group packet0741_membership
  · exact packet_mem_of_chunk packets030_group packet0742_membership
  · exact packet_mem_of_chunk packets030_group packet0743_membership
  · exact packet_mem_of_chunk packets031_group packet0744_membership

def slice041Packets : List StripRowPacket :=
  [packet0687, packet0688, packet0689, packet0690, packet0699, packet0700,
   packet0701, packet0702, packet0728, packet0730, packet0732, packet0734,
   packet0741, packet0742, packet0743, packet0744]

def slice041 : GridSlice := closedSliceOfPackets 76 80 slice041Packets

private theorem slice041_checked_local : checkSlice slice041.vertical 64 slice041 = true := by
  decide +kernel

theorem slice041_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice041 = true := by
  apply sliceCheck_of_packets slice041_checked_local
  intro p hp
  simp only [slice041Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets028_group packet0687_membership
  · exact packet_mem_of_chunk packets028_group packet0688_membership
  · exact packet_mem_of_chunk packets028_group packet0689_membership
  · exact packet_mem_of_chunk packets028_group packet0690_membership
  · exact packet_mem_of_chunk packets029_group packet0699_membership
  · exact packet_mem_of_chunk packets029_group packet0700_membership
  · exact packet_mem_of_chunk packets029_group packet0701_membership
  · exact packet_mem_of_chunk packets029_group packet0702_membership
  · exact packet_mem_of_chunk packets030_group packet0728_membership
  · exact packet_mem_of_chunk packets030_group packet0730_membership
  · exact packet_mem_of_chunk packets030_group packet0732_membership
  · exact packet_mem_of_chunk packets030_group packet0734_membership
  · exact packet_mem_of_chunk packets030_group packet0741_membership
  · exact packet_mem_of_chunk packets030_group packet0742_membership
  · exact packet_mem_of_chunk packets030_group packet0743_membership
  · exact packet_mem_of_chunk packets031_group packet0744_membership

def slice042Packets : List StripRowPacket :=
  [packet0703, packet0704, packet0707, packet0708, packet0711, packet0712,
   packet0715, packet0716, packet0745, packet0747, packet0752, packet0754,
   packet0760, packet0761, packet0764, packet0765]

def slice042 : GridSlice := closedSliceOfPackets 80 84 slice042Packets

private theorem slice042_checked_local : checkSlice slice042.vertical 64 slice042 = true := by
  decide +kernel

theorem slice042_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice042 = true := by
  apply sliceCheck_of_packets slice042_checked_local
  intro p hp
  simp only [slice042Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets029_group packet0703_membership
  · exact packet_mem_of_chunk packets029_group packet0704_membership
  · exact packet_mem_of_chunk packets029_group packet0707_membership
  · exact packet_mem_of_chunk packets029_group packet0708_membership
  · exact packet_mem_of_chunk packets029_group packet0711_membership
  · exact packet_mem_of_chunk packets029_group packet0712_membership
  · exact packet_mem_of_chunk packets029_group packet0715_membership
  · exact packet_mem_of_chunk packets029_group packet0716_membership
  · exact packet_mem_of_chunk packets031_group packet0745_membership
  · exact packet_mem_of_chunk packets031_group packet0747_membership
  · exact packet_mem_of_chunk packets031_group packet0752_membership
  · exact packet_mem_of_chunk packets031_group packet0754_membership
  · exact packet_mem_of_chunk packets031_group packet0760_membership
  · exact packet_mem_of_chunk packets031_group packet0761_membership
  · exact packet_mem_of_chunk packets031_group packet0764_membership
  · exact packet_mem_of_chunk packets031_group packet0765_membership

def slice043Packets : List StripRowPacket :=
  [packet0703, packet0704, packet0707, packet0708, packet0711, packet0712,
   packet0715, packet0716, packet0746, packet0748, packet0753, packet0755,
   packet0760, packet0761, packet0764, packet0765]

def slice043 : GridSlice := closedSliceOfPackets 84 88 slice043Packets

private theorem slice043_checked_local : checkSlice slice043.vertical 64 slice043 = true := by
  decide +kernel

theorem slice043_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice043 = true := by
  apply sliceCheck_of_packets slice043_checked_local
  intro p hp
  simp only [slice043Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets029_group packet0703_membership
  · exact packet_mem_of_chunk packets029_group packet0704_membership
  · exact packet_mem_of_chunk packets029_group packet0707_membership
  · exact packet_mem_of_chunk packets029_group packet0708_membership
  · exact packet_mem_of_chunk packets029_group packet0711_membership
  · exact packet_mem_of_chunk packets029_group packet0712_membership
  · exact packet_mem_of_chunk packets029_group packet0715_membership
  · exact packet_mem_of_chunk packets029_group packet0716_membership
  · exact packet_mem_of_chunk packets031_group packet0746_membership
  · exact packet_mem_of_chunk packets031_group packet0748_membership
  · exact packet_mem_of_chunk packets031_group packet0753_membership
  · exact packet_mem_of_chunk packets031_group packet0755_membership
  · exact packet_mem_of_chunk packets031_group packet0760_membership
  · exact packet_mem_of_chunk packets031_group packet0761_membership
  · exact packet_mem_of_chunk packets031_group packet0764_membership
  · exact packet_mem_of_chunk packets031_group packet0765_membership

def slice044Packets : List StripRowPacket :=
  [packet0705, packet0706, packet0709, packet0710, packet0713, packet0714,
   packet0717, packet0718, packet0749, packet0750, packet0756, packet0758,
   packet0762, packet0763, packet0766, packet0767]

def slice044 : GridSlice := closedSliceOfPackets 88 92 slice044Packets

private theorem slice044_checked_local : checkSlice slice044.vertical 64 slice044 = true := by
  decide +kernel

theorem slice044_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice044 = true := by
  apply sliceCheck_of_packets slice044_checked_local
  intro p hp
  simp only [slice044Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets029_group packet0705_membership
  · exact packet_mem_of_chunk packets029_group packet0706_membership
  · exact packet_mem_of_chunk packets029_group packet0709_membership
  · exact packet_mem_of_chunk packets029_group packet0710_membership
  · exact packet_mem_of_chunk packets029_group packet0713_membership
  · exact packet_mem_of_chunk packets029_group packet0714_membership
  · exact packet_mem_of_chunk packets029_group packet0717_membership
  · exact packet_mem_of_chunk packets029_group packet0718_membership
  · exact packet_mem_of_chunk packets031_group packet0749_membership
  · exact packet_mem_of_chunk packets031_group packet0750_membership
  · exact packet_mem_of_chunk packets031_group packet0756_membership
  · exact packet_mem_of_chunk packets031_group packet0758_membership
  · exact packet_mem_of_chunk packets031_group packet0762_membership
  · exact packet_mem_of_chunk packets031_group packet0763_membership
  · exact packet_mem_of_chunk packets031_group packet0766_membership
  · exact packet_mem_of_chunk packets031_group packet0767_membership

def slice045Packets : List StripRowPacket :=
  [packet0705, packet0706, packet0709, packet0710, packet0713, packet0714,
   packet0717, packet0718, packet0749, packet0751, packet0757, packet0759,
   packet0762, packet0763, packet0766, packet0767]

def slice045 : GridSlice := closedSliceOfPackets 92 96 slice045Packets

private theorem slice045_checked_local : checkSlice slice045.vertical 64 slice045 = true := by
  decide +kernel

theorem slice045_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice045 = true := by
  apply sliceCheck_of_packets slice045_checked_local
  intro p hp
  simp only [slice045Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets029_group packet0705_membership
  · exact packet_mem_of_chunk packets029_group packet0706_membership
  · exact packet_mem_of_chunk packets029_group packet0709_membership
  · exact packet_mem_of_chunk packets029_group packet0710_membership
  · exact packet_mem_of_chunk packets029_group packet0713_membership
  · exact packet_mem_of_chunk packets029_group packet0714_membership
  · exact packet_mem_of_chunk packets029_group packet0717_membership
  · exact packet_mem_of_chunk packets029_group packet0718_membership
  · exact packet_mem_of_chunk packets031_group packet0749_membership
  · exact packet_mem_of_chunk packets031_group packet0751_membership
  · exact packet_mem_of_chunk packets031_group packet0757_membership
  · exact packet_mem_of_chunk packets031_group packet0759_membership
  · exact packet_mem_of_chunk packets031_group packet0762_membership
  · exact packet_mem_of_chunk packets031_group packet0763_membership
  · exact packet_mem_of_chunk packets031_group packet0766_membership
  · exact packet_mem_of_chunk packets031_group packet0767_membership

def slice046Packets : List StripRowPacket :=
  [packet0768, packet0769, packet0772, packet0773, packet0784, packet0785,
   packet0788, packet0789, packet0800, packet0802, packet0807, packet0809,
   packet0831, packet0832, packet0835, packet0836]

def slice046 : GridSlice := closedSliceOfPackets 96 100 slice046Packets

private theorem slice046_checked_local : checkSlice slice046.vertical 64 slice046 = true := by
  decide +kernel

theorem slice046_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice046 = true := by
  apply sliceCheck_of_packets slice046_checked_local
  intro p hp
  simp only [slice046Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets032_group packet0768_membership
  · exact packet_mem_of_chunk packets032_group packet0769_membership
  · exact packet_mem_of_chunk packets032_group packet0772_membership
  · exact packet_mem_of_chunk packets032_group packet0773_membership
  · exact packet_mem_of_chunk packets032_group packet0784_membership
  · exact packet_mem_of_chunk packets032_group packet0785_membership
  · exact packet_mem_of_chunk packets032_group packet0788_membership
  · exact packet_mem_of_chunk packets032_group packet0789_membership
  · exact packet_mem_of_chunk packets033_group packet0800_membership
  · exact packet_mem_of_chunk packets033_group packet0802_membership
  · exact packet_mem_of_chunk packets033_group packet0807_membership
  · exact packet_mem_of_chunk packets033_group packet0809_membership
  · exact packet_mem_of_chunk packets034_group packet0831_membership
  · exact packet_mem_of_chunk packets034_group packet0832_membership
  · exact packet_mem_of_chunk packets034_group packet0835_membership
  · exact packet_mem_of_chunk packets034_group packet0836_membership

def slice047Packets : List StripRowPacket :=
  [packet0768, packet0769, packet0772, packet0773, packet0784, packet0785,
   packet0788, packet0789, packet0801, packet0803, packet0808, packet0810,
   packet0831, packet0832, packet0835, packet0836]

def slice047 : GridSlice := closedSliceOfPackets 100 104 slice047Packets

private theorem slice047_checked_local : checkSlice slice047.vertical 64 slice047 = true := by
  decide +kernel

theorem slice047_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice047 = true := by
  apply sliceCheck_of_packets slice047_checked_local
  intro p hp
  simp only [slice047Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets032_group packet0768_membership
  · exact packet_mem_of_chunk packets032_group packet0769_membership
  · exact packet_mem_of_chunk packets032_group packet0772_membership
  · exact packet_mem_of_chunk packets032_group packet0773_membership
  · exact packet_mem_of_chunk packets032_group packet0784_membership
  · exact packet_mem_of_chunk packets032_group packet0785_membership
  · exact packet_mem_of_chunk packets032_group packet0788_membership
  · exact packet_mem_of_chunk packets032_group packet0789_membership
  · exact packet_mem_of_chunk packets033_group packet0801_membership
  · exact packet_mem_of_chunk packets033_group packet0803_membership
  · exact packet_mem_of_chunk packets033_group packet0808_membership
  · exact packet_mem_of_chunk packets033_group packet0810_membership
  · exact packet_mem_of_chunk packets034_group packet0831_membership
  · exact packet_mem_of_chunk packets034_group packet0832_membership
  · exact packet_mem_of_chunk packets034_group packet0835_membership
  · exact packet_mem_of_chunk packets034_group packet0836_membership


end RKCert.ReviewedNative.ThreeInteriorPencil
