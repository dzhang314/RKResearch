module

public import RKCert.ERKOrderNineGoodPrimeNatSelector
import Lean.Elab.Tactic.Cbv

@[expose] public section

namespace RKCert.GoodPrimeDense.NatRow3

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

def selector : NatSelectorDatum 1319 where
  split :=
    { rel := [1289, 432, 105, 643, 40, 610]
      knots := ![[145, 1298, 660, 1208, 386, 949], [387, 116, 154, 212, 1147, 693], [806, 456, 943, 952, 256, 466], [1302, 767, 881, 266, 849, 530]]
      inv := fun _ _ _ => [112, 808, 554, 812, 122, 807] }
  hSlot := 1
  uSlot := 0
  vSlot := 3
  hi := ![[1095, 250, 1064, 42, 428, 826], [], [369, 150, 970, 562, 149, 1017], [585, 630, 463, 687, 755, 369]]
  ui := ![[], [], [94, 709, 498, 1219, 1062, 1276], [250, 1181, 393, 1075, 1103, 278]]
  vi := ![[], [], [326, 573, 1202, 267, 475, 796], []]

private def slotH := selector.split.knots selector.hSlot
private def slotU := selector.split.knots selector.uSlot
private def slotV := selector.split.knots selector.vSlot
private def dInv := constant (naturalPrime 1319) 581

private theorem terminal_eq :
    terminalRecipe selector.split.ops slotH slotU slotV (naturalParameter 1319) dInv = [283, 819, 678, 1308, 54, 479] := by cbv

theorem checked : selector.Checked 581 where
  pos := by decide +kernel
  split := by unfold NatSplitDatum.splitCheck; cbv
  h a ha := by fin_cases a <;> first | contradiction | (unfold NatSelectorDatum.hCheck; cbv)
  u b hb hbu := by fin_cases b <;> first | contradiction | (unfold NatSelectorDatum.uCheck; cbv)
  v c hc hcu hcv := by fin_cases c <;> first | contradiction | (unfold NatSelectorDatum.vCheck; cbv)
  terminal := by
    change selector.split.ops.mul
      (terminalRecipe selector.split.ops slotH slotU slotV (naturalParameter 1319) dInv) [112, 808, 554, 812, 122, 807] = [1]
    rw [terminal_eq]
    cbv

end RKCert.GoodPrimeDense.NatRow3
