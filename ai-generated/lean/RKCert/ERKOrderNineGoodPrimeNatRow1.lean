module

public import RKCert.ERKOrderNineGoodPrimeNatSelector
import Lean.Elab.Tactic.Cbv

@[expose] public section

namespace RKCert.GoodPrimeDense.NatRow1

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

def selector : NatSelectorDatum 1319 where
  split :=
    { rel := [698, 842, 326]
      knots := ![[28, 677, 126], [633, 401, 100], [698, 315, 654], [1281, 1244, 439]]
      inv := fun _ _ _ => [598, 686, 92] }
  hSlot := 3
  uSlot := 2
  vSlot := 0
  hi := ![[829, 887, 871], [161, 728, 834], [627, 1161, 1069], []]
  ui := ![[1093, 1230, 931], [882, 389, 1213], [], []]
  vi := ![[], [797, 778, 930], [], []]

private def slotH := selector.split.knots selector.hSlot
private def slotU := selector.split.knots selector.uSlot
private def slotV := selector.split.knots selector.vSlot
private def dInv := constant (naturalPrime 1319) 581

private theorem terminal_eq :
    terminalRecipe selector.split.ops slotH slotU slotV (naturalParameter 1319) dInv = [573, 1118, 408] := by cbv

theorem checked : selector.Checked 581 where
  pos := by decide +kernel
  split := by unfold NatSplitDatum.splitCheck; cbv
  h a ha := by fin_cases a <;> first | contradiction | (unfold NatSelectorDatum.hCheck; cbv)
  u b hb hbu := by fin_cases b <;> first | contradiction | (unfold NatSelectorDatum.uCheck; cbv)
  v c hc hcu hcv := by fin_cases c <;> first | contradiction | (unfold NatSelectorDatum.vCheck; cbv)
  terminal := by
    change selector.split.ops.mul
      (terminalRecipe selector.split.ops slotH slotU slotV (naturalParameter 1319) dInv) [598, 686, 92] = [1]
    rw [terminal_eq]
    cbv

end RKCert.GoodPrimeDense.NatRow1
