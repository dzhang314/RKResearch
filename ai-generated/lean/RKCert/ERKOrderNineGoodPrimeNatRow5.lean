module

public import RKCert.ERKOrderNineGoodPrimeNatSelector
import Lean.Elab.Tactic.Cbv

@[expose] public section

namespace RKCert.GoodPrimeDense.NatRow5

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

def selector : NatSelectorDatum 1319 where
  split :=
    { rel := [650, 965, 48, 1075, 218, 656, 602]
      knots := ![[77, 1182, 957, 442, 934, 51, 97], [331, 844, 1018, 666, 703, 236, 1130], [1097, 1086, 140, 800, 360, 461, 79], [1135, 844, 523, 730, 641, 571, 13]]
      inv := fun _ _ _ => [674, 765, 168, 887, 946, 1025, 1012] }
  hSlot := 3
  uSlot := 2
  vSlot := 1
  hi := ![[115, 656, 514, 417, 863, 56, 1023], [941, 942, 1020, 30, 53, 842, 814], [402, 845, 918, 884, 704, 415, 919], []]
  ui := ![[763, 202, 1152, 1239, 1278, 516, 628], [69, 673, 224, 154, 638, 273, 23], [], []]
  vi := ![[34, 670, 400, 1099, 486, 1119, 686], [], [], []]

private def slotH := selector.split.knots selector.hSlot
private def slotU := selector.split.knots selector.uSlot
private def slotV := selector.split.knots selector.vSlot
private def dInv := constant (naturalPrime 1319) 581

private theorem terminal_eq :
    terminalRecipe selector.split.ops slotH slotU slotV (naturalParameter 1319) dInv = [839, 118, 234, 899, 571, 747, 557] := by cbv

theorem checked : selector.Checked 581 where
  pos := by decide +kernel
  split := by unfold NatSplitDatum.splitCheck; cbv
  h a ha := by fin_cases a <;> first | contradiction | (unfold NatSelectorDatum.hCheck; cbv)
  u b hb hbu := by fin_cases b <;> first | contradiction | (unfold NatSelectorDatum.uCheck; cbv)
  v c hc hcu hcv := by fin_cases c <;> first | contradiction | (unfold NatSelectorDatum.vCheck; cbv)
  terminal := by
    change selector.split.ops.mul
      (terminalRecipe selector.split.ops slotH slotU slotV (naturalParameter 1319) dInv) [674, 765, 168, 887, 946, 1025, 1012] = [1]
    rw [terminal_eq]
    cbv

end RKCert.GoodPrimeDense.NatRow5
