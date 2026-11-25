module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorLiteralStripRows

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

def slice048Packets : List StripRowPacket :=
  [packet0770, packet0771, packet0774, packet0775, packet0786, packet0787,
   packet0790, packet0791, packet0804, packet0805, packet0811, packet0813,
   packet0833, packet0834, packet0837, packet0838]

def slice048 : GridSlice := closedSliceOfPackets 104 108 slice048Packets

private theorem slice048_checked_local : checkSlice slice048.vertical 64 slice048 = true := by
  decide +kernel

theorem slice048_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice048 = true := by
  apply sliceCheck_of_packets slice048_checked_local
  intro p hp
  simp only [slice048Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets032_group packet0770_membership
  · exact packet_mem_of_chunk packets032_group packet0771_membership
  · exact packet_mem_of_chunk packets032_group packet0774_membership
  · exact packet_mem_of_chunk packets032_group packet0775_membership
  · exact packet_mem_of_chunk packets032_group packet0786_membership
  · exact packet_mem_of_chunk packets032_group packet0787_membership
  · exact packet_mem_of_chunk packets032_group packet0790_membership
  · exact packet_mem_of_chunk packets032_group packet0791_membership
  · exact packet_mem_of_chunk packets033_group packet0804_membership
  · exact packet_mem_of_chunk packets033_group packet0805_membership
  · exact packet_mem_of_chunk packets033_group packet0811_membership
  · exact packet_mem_of_chunk packets033_group packet0813_membership
  · exact packet_mem_of_chunk packets034_group packet0833_membership
  · exact packet_mem_of_chunk packets034_group packet0834_membership
  · exact packet_mem_of_chunk packets034_group packet0837_membership
  · exact packet_mem_of_chunk packets034_group packet0838_membership

def slice049Packets : List StripRowPacket :=
  [packet0770, packet0771, packet0774, packet0775, packet0786, packet0787,
   packet0790, packet0791, packet0804, packet0806, packet0812, packet0814,
   packet0833, packet0834, packet0837, packet0838]

def slice049 : GridSlice := closedSliceOfPackets 108 112 slice049Packets

private theorem slice049_checked_local : checkSlice slice049.vertical 64 slice049 = true := by
  decide +kernel

theorem slice049_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice049 = true := by
  apply sliceCheck_of_packets slice049_checked_local
  intro p hp
  simp only [slice049Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets032_group packet0770_membership
  · exact packet_mem_of_chunk packets032_group packet0771_membership
  · exact packet_mem_of_chunk packets032_group packet0774_membership
  · exact packet_mem_of_chunk packets032_group packet0775_membership
  · exact packet_mem_of_chunk packets032_group packet0786_membership
  · exact packet_mem_of_chunk packets032_group packet0787_membership
  · exact packet_mem_of_chunk packets032_group packet0790_membership
  · exact packet_mem_of_chunk packets032_group packet0791_membership
  · exact packet_mem_of_chunk packets033_group packet0804_membership
  · exact packet_mem_of_chunk packets033_group packet0806_membership
  · exact packet_mem_of_chunk packets033_group packet0812_membership
  · exact packet_mem_of_chunk packets033_group packet0814_membership
  · exact packet_mem_of_chunk packets034_group packet0833_membership
  · exact packet_mem_of_chunk packets034_group packet0834_membership
  · exact packet_mem_of_chunk packets034_group packet0837_membership
  · exact packet_mem_of_chunk packets034_group packet0838_membership

def slice050Packets : List StripRowPacket :=
  [packet0776, packet0777, packet0780, packet0781, packet0792, packet0793,
   packet0796, packet0797, packet0815, packet0817, packet0823, packet0825,
   packet0839, packet0840, packet0843, packet0844]

def slice050 : GridSlice := closedSliceOfPackets 112 116 slice050Packets

private theorem slice050_checked_local : checkSlice slice050.vertical 64 slice050 = true := by
  decide +kernel

theorem slice050_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice050 = true := by
  apply sliceCheck_of_packets slice050_checked_local
  intro p hp
  simp only [slice050Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets032_group packet0776_membership
  · exact packet_mem_of_chunk packets032_group packet0777_membership
  · exact packet_mem_of_chunk packets032_group packet0780_membership
  · exact packet_mem_of_chunk packets032_group packet0781_membership
  · exact packet_mem_of_chunk packets033_group packet0792_membership
  · exact packet_mem_of_chunk packets033_group packet0793_membership
  · exact packet_mem_of_chunk packets033_group packet0796_membership
  · exact packet_mem_of_chunk packets033_group packet0797_membership
  · exact packet_mem_of_chunk packets033_group packet0815_membership
  · exact packet_mem_of_chunk packets034_group packet0817_membership
  · exact packet_mem_of_chunk packets034_group packet0823_membership
  · exact packet_mem_of_chunk packets034_group packet0825_membership
  · exact packet_mem_of_chunk packets034_group packet0839_membership
  · exact packet_mem_of_chunk packets035_group packet0840_membership
  · exact packet_mem_of_chunk packets035_group packet0843_membership
  · exact packet_mem_of_chunk packets035_group packet0844_membership

def slice051Packets : List StripRowPacket :=
  [packet0776, packet0777, packet0780, packet0781, packet0792, packet0793,
   packet0796, packet0797, packet0816, packet0818, packet0824, packet0826,
   packet0839, packet0840, packet0843, packet0844]

def slice051 : GridSlice := closedSliceOfPackets 116 120 slice051Packets

private theorem slice051_checked_local : checkSlice slice051.vertical 64 slice051 = true := by
  decide +kernel

theorem slice051_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice051 = true := by
  apply sliceCheck_of_packets slice051_checked_local
  intro p hp
  simp only [slice051Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets032_group packet0776_membership
  · exact packet_mem_of_chunk packets032_group packet0777_membership
  · exact packet_mem_of_chunk packets032_group packet0780_membership
  · exact packet_mem_of_chunk packets032_group packet0781_membership
  · exact packet_mem_of_chunk packets033_group packet0792_membership
  · exact packet_mem_of_chunk packets033_group packet0793_membership
  · exact packet_mem_of_chunk packets033_group packet0796_membership
  · exact packet_mem_of_chunk packets033_group packet0797_membership
  · exact packet_mem_of_chunk packets034_group packet0816_membership
  · exact packet_mem_of_chunk packets034_group packet0818_membership
  · exact packet_mem_of_chunk packets034_group packet0824_membership
  · exact packet_mem_of_chunk packets034_group packet0826_membership
  · exact packet_mem_of_chunk packets034_group packet0839_membership
  · exact packet_mem_of_chunk packets035_group packet0840_membership
  · exact packet_mem_of_chunk packets035_group packet0843_membership
  · exact packet_mem_of_chunk packets035_group packet0844_membership

def slice052Packets : List StripRowPacket :=
  [packet0778, packet0779, packet0782, packet0783, packet0794, packet0795,
   packet0798, packet0799, packet0819, packet0821, packet0827, packet0829,
   packet0841, packet0842, packet0845, packet0846]

def slice052 : GridSlice := closedSliceOfPackets 120 124 slice052Packets

private theorem slice052_checked_local : checkSlice slice052.vertical 64 slice052 = true := by
  decide +kernel

theorem slice052_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice052 = true := by
  apply sliceCheck_of_packets slice052_checked_local
  intro p hp
  simp only [slice052Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets032_group packet0778_membership
  · exact packet_mem_of_chunk packets032_group packet0779_membership
  · exact packet_mem_of_chunk packets032_group packet0782_membership
  · exact packet_mem_of_chunk packets032_group packet0783_membership
  · exact packet_mem_of_chunk packets033_group packet0794_membership
  · exact packet_mem_of_chunk packets033_group packet0795_membership
  · exact packet_mem_of_chunk packets033_group packet0798_membership
  · exact packet_mem_of_chunk packets033_group packet0799_membership
  · exact packet_mem_of_chunk packets034_group packet0819_membership
  · exact packet_mem_of_chunk packets034_group packet0821_membership
  · exact packet_mem_of_chunk packets034_group packet0827_membership
  · exact packet_mem_of_chunk packets034_group packet0829_membership
  · exact packet_mem_of_chunk packets035_group packet0841_membership
  · exact packet_mem_of_chunk packets035_group packet0842_membership
  · exact packet_mem_of_chunk packets035_group packet0845_membership
  · exact packet_mem_of_chunk packets035_group packet0846_membership

def slice053Packets : List StripRowPacket :=
  [packet0778, packet0779, packet0782, packet0783, packet0794, packet0795,
   packet0798, packet0799, packet0820, packet0822, packet0828, packet0830,
   packet0841, packet0842, packet0845, packet0846]

def slice053 : GridSlice := closedSliceOfPackets 124 128 slice053Packets

private theorem slice053_checked_local : checkSlice slice053.vertical 64 slice053 = true := by
  decide +kernel

theorem slice053_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice053 = true := by
  apply sliceCheck_of_packets slice053_checked_local
  intro p hp
  simp only [slice053Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets032_group packet0778_membership
  · exact packet_mem_of_chunk packets032_group packet0779_membership
  · exact packet_mem_of_chunk packets032_group packet0782_membership
  · exact packet_mem_of_chunk packets032_group packet0783_membership
  · exact packet_mem_of_chunk packets033_group packet0794_membership
  · exact packet_mem_of_chunk packets033_group packet0795_membership
  · exact packet_mem_of_chunk packets033_group packet0798_membership
  · exact packet_mem_of_chunk packets033_group packet0799_membership
  · exact packet_mem_of_chunk packets034_group packet0820_membership
  · exact packet_mem_of_chunk packets034_group packet0822_membership
  · exact packet_mem_of_chunk packets034_group packet0828_membership
  · exact packet_mem_of_chunk packets034_group packet0830_membership
  · exact packet_mem_of_chunk packets035_group packet0841_membership
  · exact packet_mem_of_chunk packets035_group packet0842_membership
  · exact packet_mem_of_chunk packets035_group packet0845_membership
  · exact packet_mem_of_chunk packets035_group packet0846_membership

def slice054Packets : List StripRowPacket :=
  [packet0847, packet0849, packet0850, packet0859, packet0860, packet0863,
   packet0864, packet0901, packet0903, packet0909, packet0911, packet0933,
   packet0934, packet0937, packet0938]

def slice054 : GridSlice := closedSliceOfPackets 128 132 slice054Packets

private theorem slice054_checked_local : checkSlice slice054.vertical 64 slice054 = true := by
  decide +kernel

theorem slice054_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice054 = true := by
  apply sliceCheck_of_packets slice054_checked_local
  intro p hp
  simp only [slice054Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets035_group packet0847_membership
  · exact packet_mem_of_chunk packets035_group packet0849_membership
  · exact packet_mem_of_chunk packets035_group packet0850_membership
  · exact packet_mem_of_chunk packets035_group packet0859_membership
  · exact packet_mem_of_chunk packets035_group packet0860_membership
  · exact packet_mem_of_chunk packets035_group packet0863_membership
  · exact packet_mem_of_chunk packets036_group packet0864_membership
  · exact packet_mem_of_chunk packets037_group packet0901_membership
  · exact packet_mem_of_chunk packets037_group packet0903_membership
  · exact packet_mem_of_chunk packets037_group packet0909_membership
  · exact packet_mem_of_chunk packets037_group packet0911_membership
  · exact packet_mem_of_chunk packets038_group packet0933_membership
  · exact packet_mem_of_chunk packets038_group packet0934_membership
  · exact packet_mem_of_chunk packets039_group packet0937_membership
  · exact packet_mem_of_chunk packets039_group packet0938_membership

def slice055Packets : List StripRowPacket :=
  [packet0847, packet0849, packet0850, packet0859, packet0860, packet0863,
   packet0864, packet0902, packet0904, packet0910, packet0912, packet0933,
   packet0934, packet0937, packet0938]

def slice055 : GridSlice := closedSliceOfPackets 132 136 slice055Packets

private theorem slice055_checked_local : checkSlice slice055.vertical 64 slice055 = true := by
  decide +kernel

theorem slice055_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice055 = true := by
  apply sliceCheck_of_packets slice055_checked_local
  intro p hp
  simp only [slice055Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets035_group packet0847_membership
  · exact packet_mem_of_chunk packets035_group packet0849_membership
  · exact packet_mem_of_chunk packets035_group packet0850_membership
  · exact packet_mem_of_chunk packets035_group packet0859_membership
  · exact packet_mem_of_chunk packets035_group packet0860_membership
  · exact packet_mem_of_chunk packets035_group packet0863_membership
  · exact packet_mem_of_chunk packets036_group packet0864_membership
  · exact packet_mem_of_chunk packets037_group packet0902_membership
  · exact packet_mem_of_chunk packets037_group packet0904_membership
  · exact packet_mem_of_chunk packets037_group packet0910_membership
  · exact packet_mem_of_chunk packets038_group packet0912_membership
  · exact packet_mem_of_chunk packets038_group packet0933_membership
  · exact packet_mem_of_chunk packets038_group packet0934_membership
  · exact packet_mem_of_chunk packets039_group packet0937_membership
  · exact packet_mem_of_chunk packets039_group packet0938_membership


end RKCert.ReviewedNative.ThreeInteriorPencil
