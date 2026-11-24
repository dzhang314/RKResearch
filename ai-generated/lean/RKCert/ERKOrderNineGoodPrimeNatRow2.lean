module

public import RKCert.ERKOrderNineGoodPrimeNatSelector
import Lean.Elab.Tactic.Cbv

@[expose] public section

namespace RKCert.GoodPrimeDense.NatRow2

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

def selector : NatSelectorDatum 1319 where
  split :=
    { rel := [1124, 888, 917, 1157]
      knots := ![[122, 114, 304, 702], [409, 1072, 524, 1148], [892, 286, 681, 477], [1217, 1165, 1129, 311]]
      inv := fun _ _ _ => [352, 1303, 1308, 876] }
  hSlot := 2
  uSlot := 1
  vSlot := 0
  hi := ![[731, 774, 753, 292], [492, 677, 599, 30], [], [746, 1249, 1158, 1311]]
  ui := ![[503, 1300, 696, 3], [], [], [1274, 153, 1050, 274]]
  vi := ![[], [], [], [16, 512, 123, 203]]

private def slotH := selector.split.knots selector.hSlot
private def slotU := selector.split.knots selector.uSlot
private def slotV := selector.split.knots selector.vSlot
private def dInv := constant (naturalPrime 1319) 581

private theorem terminal_eq :
    terminalRecipe selector.split.ops slotH slotU slotV (naturalParameter 1319) dInv = [800, 553, 792, 550] := by cbv

theorem checked : selector.Checked 581 where
  pos := by decide +kernel
  split := by unfold NatSplitDatum.splitCheck; cbv
  h a ha := by fin_cases a <;> first | contradiction | (unfold NatSelectorDatum.hCheck; cbv)
  u b hb hbu := by fin_cases b <;> first | contradiction | (unfold NatSelectorDatum.uCheck; cbv)
  v c hc hcu hcv := by fin_cases c <;> first | contradiction | (unfold NatSelectorDatum.vCheck; cbv)
  terminal := by
    change selector.split.ops.mul
      (terminalRecipe selector.split.ops slotH slotU slotV (naturalParameter 1319) dInv) [352, 1303, 1308, 876] = [1]
    rw [terminal_eq]
    cbv

end RKCert.GoodPrimeDense.NatRow2
