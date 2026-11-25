module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorLiteralStripRows

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

def slice056Packets : List StripRowPacket :=
  [packet0848, packet0851, packet0852, packet0861, packet0862, packet0865,
   packet0866, packet0905, packet0907, packet0913, packet0915, packet0935,
   packet0936, packet0939, packet0940]

def slice056 : GridSlice := closedSliceOfPackets 136 140 slice056Packets

private theorem slice056_checked_local : checkSlice slice056.vertical 64 slice056 = true := by
  decide +kernel

theorem slice056_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice056 = true := by
  apply sliceCheck_of_packets slice056_checked_local
  intro p hp
  simp only [slice056Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets035_group packet0848_membership
  · exact packet_mem_of_chunk packets035_group packet0851_membership
  · exact packet_mem_of_chunk packets035_group packet0852_membership
  · exact packet_mem_of_chunk packets035_group packet0861_membership
  · exact packet_mem_of_chunk packets035_group packet0862_membership
  · exact packet_mem_of_chunk packets036_group packet0865_membership
  · exact packet_mem_of_chunk packets036_group packet0866_membership
  · exact packet_mem_of_chunk packets037_group packet0905_membership
  · exact packet_mem_of_chunk packets037_group packet0907_membership
  · exact packet_mem_of_chunk packets038_group packet0913_membership
  · exact packet_mem_of_chunk packets038_group packet0915_membership
  · exact packet_mem_of_chunk packets038_group packet0935_membership
  · exact packet_mem_of_chunk packets039_group packet0936_membership
  · exact packet_mem_of_chunk packets039_group packet0939_membership
  · exact packet_mem_of_chunk packets039_group packet0940_membership

def slice057Packets : List StripRowPacket :=
  [packet0848, packet0851, packet0852, packet0861, packet0862, packet0865,
   packet0866, packet0906, packet0908, packet0914, packet0916, packet0935,
   packet0936, packet0939, packet0940]

def slice057 : GridSlice := closedSliceOfPackets 140 144 slice057Packets

private theorem slice057_checked_local : checkSlice slice057.vertical 64 slice057 = true := by
  decide +kernel

theorem slice057_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice057 = true := by
  apply sliceCheck_of_packets slice057_checked_local
  intro p hp
  simp only [slice057Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets035_group packet0848_membership
  · exact packet_mem_of_chunk packets035_group packet0851_membership
  · exact packet_mem_of_chunk packets035_group packet0852_membership
  · exact packet_mem_of_chunk packets035_group packet0861_membership
  · exact packet_mem_of_chunk packets035_group packet0862_membership
  · exact packet_mem_of_chunk packets036_group packet0865_membership
  · exact packet_mem_of_chunk packets036_group packet0866_membership
  · exact packet_mem_of_chunk packets037_group packet0906_membership
  · exact packet_mem_of_chunk packets037_group packet0908_membership
  · exact packet_mem_of_chunk packets038_group packet0914_membership
  · exact packet_mem_of_chunk packets038_group packet0916_membership
  · exact packet_mem_of_chunk packets038_group packet0935_membership
  · exact packet_mem_of_chunk packets039_group packet0936_membership
  · exact packet_mem_of_chunk packets039_group packet0939_membership
  · exact packet_mem_of_chunk packets039_group packet0940_membership

def slice058Packets : List StripRowPacket :=
  [packet0853, packet0855, packet0856, packet0867, packet0868, packet0871,
   packet0872, packet0917, packet0919, packet0925, packet0927, packet0941,
   packet0942, packet0945, packet0946]

def slice058 : GridSlice := closedSliceOfPackets 144 148 slice058Packets

private theorem slice058_checked_local : checkSlice slice058.vertical 64 slice058 = true := by
  decide +kernel

theorem slice058_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice058 = true := by
  apply sliceCheck_of_packets slice058_checked_local
  intro p hp
  simp only [slice058Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets035_group packet0853_membership
  · exact packet_mem_of_chunk packets035_group packet0855_membership
  · exact packet_mem_of_chunk packets035_group packet0856_membership
  · exact packet_mem_of_chunk packets036_group packet0867_membership
  · exact packet_mem_of_chunk packets036_group packet0868_membership
  · exact packet_mem_of_chunk packets036_group packet0871_membership
  · exact packet_mem_of_chunk packets036_group packet0872_membership
  · exact packet_mem_of_chunk packets038_group packet0917_membership
  · exact packet_mem_of_chunk packets038_group packet0919_membership
  · exact packet_mem_of_chunk packets038_group packet0925_membership
  · exact packet_mem_of_chunk packets038_group packet0927_membership
  · exact packet_mem_of_chunk packets039_group packet0941_membership
  · exact packet_mem_of_chunk packets039_group packet0942_membership
  · exact packet_mem_of_chunk packets039_group packet0945_membership
  · exact packet_mem_of_chunk packets039_group packet0946_membership

def slice059Packets : List StripRowPacket :=
  [packet0853, packet0855, packet0856, packet0867, packet0868, packet0871,
   packet0872, packet0918, packet0920, packet0926, packet0928, packet0941,
   packet0942, packet0945, packet0946]

def slice059 : GridSlice := closedSliceOfPackets 148 152 slice059Packets

private theorem slice059_checked_local : checkSlice slice059.vertical 64 slice059 = true := by
  decide +kernel

theorem slice059_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice059 = true := by
  apply sliceCheck_of_packets slice059_checked_local
  intro p hp
  simp only [slice059Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets035_group packet0853_membership
  · exact packet_mem_of_chunk packets035_group packet0855_membership
  · exact packet_mem_of_chunk packets035_group packet0856_membership
  · exact packet_mem_of_chunk packets036_group packet0867_membership
  · exact packet_mem_of_chunk packets036_group packet0868_membership
  · exact packet_mem_of_chunk packets036_group packet0871_membership
  · exact packet_mem_of_chunk packets036_group packet0872_membership
  · exact packet_mem_of_chunk packets038_group packet0918_membership
  · exact packet_mem_of_chunk packets038_group packet0920_membership
  · exact packet_mem_of_chunk packets038_group packet0926_membership
  · exact packet_mem_of_chunk packets038_group packet0928_membership
  · exact packet_mem_of_chunk packets039_group packet0941_membership
  · exact packet_mem_of_chunk packets039_group packet0942_membership
  · exact packet_mem_of_chunk packets039_group packet0945_membership
  · exact packet_mem_of_chunk packets039_group packet0946_membership

def slice060Packets : List StripRowPacket :=
  [packet0854, packet0857, packet0858, packet0869, packet0870, packet0873,
   packet0874, packet0921, packet0923, packet0929, packet0931, packet0943,
   packet0944, packet0947, packet0948]

def slice060 : GridSlice := closedSliceOfPackets 152 156 slice060Packets

private theorem slice060_checked_local : checkSlice slice060.vertical 64 slice060 = true := by
  decide +kernel

theorem slice060_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice060 = true := by
  apply sliceCheck_of_packets slice060_checked_local
  intro p hp
  simp only [slice060Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets035_group packet0854_membership
  · exact packet_mem_of_chunk packets035_group packet0857_membership
  · exact packet_mem_of_chunk packets035_group packet0858_membership
  · exact packet_mem_of_chunk packets036_group packet0869_membership
  · exact packet_mem_of_chunk packets036_group packet0870_membership
  · exact packet_mem_of_chunk packets036_group packet0873_membership
  · exact packet_mem_of_chunk packets036_group packet0874_membership
  · exact packet_mem_of_chunk packets038_group packet0921_membership
  · exact packet_mem_of_chunk packets038_group packet0923_membership
  · exact packet_mem_of_chunk packets038_group packet0929_membership
  · exact packet_mem_of_chunk packets038_group packet0931_membership
  · exact packet_mem_of_chunk packets039_group packet0943_membership
  · exact packet_mem_of_chunk packets039_group packet0944_membership
  · exact packet_mem_of_chunk packets039_group packet0947_membership
  · exact packet_mem_of_chunk packets039_group packet0948_membership

def slice061Packets : List StripRowPacket :=
  [packet0854, packet0857, packet0858, packet0869, packet0870, packet0873,
   packet0874, packet0922, packet0924, packet0930, packet0932, packet0943,
   packet0944, packet0947, packet0948]

def slice061 : GridSlice := closedSliceOfPackets 156 160 slice061Packets

private theorem slice061_checked_local : checkSlice slice061.vertical 64 slice061 = true := by
  decide +kernel

theorem slice061_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice061 = true := by
  apply sliceCheck_of_packets slice061_checked_local
  intro p hp
  simp only [slice061Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets035_group packet0854_membership
  · exact packet_mem_of_chunk packets035_group packet0857_membership
  · exact packet_mem_of_chunk packets035_group packet0858_membership
  · exact packet_mem_of_chunk packets036_group packet0869_membership
  · exact packet_mem_of_chunk packets036_group packet0870_membership
  · exact packet_mem_of_chunk packets036_group packet0873_membership
  · exact packet_mem_of_chunk packets036_group packet0874_membership
  · exact packet_mem_of_chunk packets038_group packet0922_membership
  · exact packet_mem_of_chunk packets038_group packet0924_membership
  · exact packet_mem_of_chunk packets038_group packet0930_membership
  · exact packet_mem_of_chunk packets038_group packet0932_membership
  · exact packet_mem_of_chunk packets039_group packet0943_membership
  · exact packet_mem_of_chunk packets039_group packet0944_membership
  · exact packet_mem_of_chunk packets039_group packet0947_membership
  · exact packet_mem_of_chunk packets039_group packet0948_membership

def slice062Packets : List StripRowPacket :=
  [packet0875, packet0876, packet0877, packet0885, packet0886, packet0889,
   packet0890, packet0949, packet0951, packet0957, packet0958, packet0961,
   packet0992, packet0993, packet0996, packet0997]

def slice062 : GridSlice := closedSliceOfPackets 160 164 slice062Packets

private theorem slice062_checked_local : checkSlice slice062.vertical 64 slice062 = true := by
  decide +kernel

theorem slice062_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice062 = true := by
  apply sliceCheck_of_packets slice062_checked_local
  intro p hp
  simp only [slice062Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets036_group packet0875_membership
  · exact packet_mem_of_chunk packets036_group packet0876_membership
  · exact packet_mem_of_chunk packets036_group packet0877_membership
  · exact packet_mem_of_chunk packets036_group packet0885_membership
  · exact packet_mem_of_chunk packets036_group packet0886_membership
  · exact packet_mem_of_chunk packets037_group packet0889_membership
  · exact packet_mem_of_chunk packets037_group packet0890_membership
  · exact packet_mem_of_chunk packets039_group packet0949_membership
  · exact packet_mem_of_chunk packets039_group packet0951_membership
  · exact packet_mem_of_chunk packets039_group packet0957_membership
  · exact packet_mem_of_chunk packets039_group packet0958_membership
  · exact packet_mem_of_chunk packets040_group packet0961_membership
  · exact packet_mem_of_chunk packets041_group packet0992_membership
  · exact packet_mem_of_chunk packets041_group packet0993_membership
  · exact packet_mem_of_chunk packets041_group packet0996_membership
  · exact packet_mem_of_chunk packets041_group packet0997_membership

def slice063Packets : List StripRowPacket :=
  [packet0875, packet0876, packet0877, packet0885, packet0886, packet0889,
   packet0890, packet0950, packet0952, packet0959, packet0960, packet0962,
   packet0992, packet0993, packet0996, packet0997]

def slice063 : GridSlice := closedSliceOfPackets 164 168 slice063Packets

private theorem slice063_checked_local : checkSlice slice063.vertical 64 slice063 = true := by
  decide +kernel

theorem slice063_checked :
    checkSlice (threeInteriorLiteralRects.map (DyadicRect.normalize 8 6)) 64 slice063 = true := by
  apply sliceCheck_of_packets slice063_checked_local
  intro p hp
  simp only [slice063Packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact packet_mem_of_chunk packets036_group packet0875_membership
  · exact packet_mem_of_chunk packets036_group packet0876_membership
  · exact packet_mem_of_chunk packets036_group packet0877_membership
  · exact packet_mem_of_chunk packets036_group packet0885_membership
  · exact packet_mem_of_chunk packets036_group packet0886_membership
  · exact packet_mem_of_chunk packets037_group packet0889_membership
  · exact packet_mem_of_chunk packets037_group packet0890_membership
  · exact packet_mem_of_chunk packets039_group packet0950_membership
  · exact packet_mem_of_chunk packets039_group packet0952_membership
  · exact packet_mem_of_chunk packets039_group packet0959_membership
  · exact packet_mem_of_chunk packets040_group packet0960_membership
  · exact packet_mem_of_chunk packets040_group packet0962_membership
  · exact packet_mem_of_chunk packets041_group packet0992_membership
  · exact packet_mem_of_chunk packets041_group packet0993_membership
  · exact packet_mem_of_chunk packets041_group packet0996_membership
  · exact packet_mem_of_chunk packets041_group packet0997_membership


end RKCert.ReviewedNative.ThreeInteriorPencil
