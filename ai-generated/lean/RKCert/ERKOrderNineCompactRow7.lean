module

public import RKCert.ERKOrderNineCompactSelector
public import RKCert.ERKOrderNineCompactTape7

@[expose] public section

namespace RKCert.CompactResidue.Row7
open RKCert.GoodPrimeDense

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def selector : NatSelectorDatum 1319 where
  split :=
    { rel := [490, 880, 186, 852, 109, 474, 380, 402, 1307, 942]
      knots := ![[342, 1093, 933, 1, 436, 1155, 401, 194, 151, 52], [453, 908, 1100, 447, 1311, 807, 1095, 710, 998, 345], [846, 622, 1164, 796, 310, 131, 490, 1262, 141, 1089], [999, 14, 760, 75, 581, 545, 652, 472, 29, 1152]]
      inv := fun _ _ _ => [970, 1316, 233, 575, 1245, 875, 521, 384, 395, 485] }
  hSlot := 2
  uSlot := 3
  vSlot := 1
  hi := ![[1296, 878, 140, 1292, 747, 212, 961, 1315, 514, 800], [828, 424, 1226, 31, 938, 710, 136, 1268, 314, 301], [], [1316, 489, 907, 953, 611, 460, 717, 1248, 234, 254]]
  ui := ![[1167, 964, 935, 256, 1283, 1168, 942, 845, 1045, 983], [856, 1055, 449, 869, 1231, 795, 846, 1170, 41, 935], [], []]
  vi := ![[819, 594, 182, 745, 430, 659, 840, 227, 894, 1105], [], [], []]

theorem checked : TapeChecked selector 581 where
  split := Tape7.splitProof
  terminal := Tape7.terminalProof
  h a ha := by
    fin_cases a
    · exact Tape7.h0Proof
    · exact Tape7.h1Proof
    · exact (ha rfl).elim
    · exact Tape7.h3Proof
  u b ha hb := by
    fin_cases b
    · exact Tape7.u0Proof
    · exact Tape7.u1Proof
    · exact (ha rfl).elim
    · exact (hb rfl).elim
  v c ha hb hc := by
    fin_cases c
    · exact Tape7.v0Proof
    · exact (hc rfl).elim
    · exact (ha rfl).elim
    · exact (hb rfl).elim

end RKCert.CompactResidue.Row7
