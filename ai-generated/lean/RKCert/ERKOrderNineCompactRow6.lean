module

public import RKCert.ERKOrderNineCompactSelector
public import RKCert.ERKOrderNineCompactTape6

@[expose] public section

namespace RKCert.CompactResidue.Row6
open RKCert.GoodPrimeDense

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def selector : NatSelectorDatum 1319 where
  split :=
    { rel := [479, 1079, 183, 407, 799, 245, 546, 394, 999]
      knots := ![[163, 815, 731, 520, 651, 895, 160, 1101, 1124], [371, 1159, 934, 803, 1137, 1086, 171, 82, 949], [817, 875, 292, 492, 355, 648, 870, 845, 1293], [1289, 1107, 681, 823, 495, 9, 118, 610, 591]]
      inv := fun _ _ _ => [410, 657, 1099, 69, 422, 438, 345, 936, 690] }
  hSlot := 0
  uSlot := 1
  vSlot := 2
  hi := ![[], [391, 444, 114, 2, 738, 1220, 512, 321, 974], [1002, 887, 656, 370, 53, 1151, 301, 672, 67], [863, 1313, 803, 662, 832, 147, 560, 249, 1282]]
  ui := ![[], [], [865, 269, 714, 351, 260, 300, 538, 135, 169], [6, 1069, 638, 908, 843, 761, 521, 75, 695]]
  vi := ![[], [], [], [233, 511, 779, 797, 270, 116, 541, 978, 42]]

theorem checked : TapeChecked selector 581 where
  split := Tape6.splitProof
  terminal := Tape6.terminalProof
  h a ha := by
    fin_cases a
    · exact (ha rfl).elim
    · exact Tape6.h1Proof
    · exact Tape6.h2Proof
    · exact Tape6.h3Proof
  u b ha hb := by
    fin_cases b
    · exact (ha rfl).elim
    · exact (hb rfl).elim
    · exact Tape6.u2Proof
    · exact Tape6.u3Proof
  v c ha hb hc := by
    fin_cases c
    · exact (ha rfl).elim
    · exact (hb rfl).elim
    · exact (hc rfl).elim
    · exact Tape6.v3Proof

end RKCert.CompactResidue.Row6
