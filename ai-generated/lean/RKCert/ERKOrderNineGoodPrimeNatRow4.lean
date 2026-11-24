module

public import RKCert.ERKOrderNineGoodPrimeNatSelector
import Lean.Elab.Tactic.Cbv

@[expose] public section

namespace RKCert.GoodPrimeDense.NatRow4

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

def selector : NatSelectorDatum 1319 where
  split :=
    { rel := [541, 1009, 1050, 432, 279, 735, 724]
      knots := ![[30, 744, 848, 22, 324, 974, 131], [699, 542, 1307, 892, 526, 1240, 656], [892, 1017, 1291, 89, 723, 952, 530], [1019, 334, 511, 316, 1065, 791, 2]]
      inv := fun _ _ _ => [461, 942, 371, 590, 264, 2, 182] }
  hSlot := 0
  uSlot := 2
  vSlot := 1
  hi := ![[], [223, 1201, 1001, 684, 1157, 503, 499], [774, 159, 604, 354, 1172, 448, 1235], [801, 218, 70, 1088, 434, 675, 250]]
  ui := ![[], [221, 107, 668, 893, 134, 821, 259], [], [173, 542, 707, 635, 1241, 571, 249]]
  vi := ![[], [], [], [35, 798, 882, 1016, 1112, 781, 763]]

private def slotH := selector.split.knots selector.hSlot
private def slotU := selector.split.knots selector.uSlot
private def slotV := selector.split.knots selector.vSlot
private def dInv := constant (naturalPrime 1319) 581

private theorem terminal_eq :
    terminalRecipe selector.split.ops slotH slotU slotV (naturalParameter 1319) dInv = [25, 383, 1156, 127, 1317, 817, 838] := by cbv

theorem checked : selector.Checked 581 where
  pos := by decide +kernel
  split := by unfold NatSplitDatum.splitCheck; cbv
  h a ha := by fin_cases a <;> first | contradiction | (unfold NatSelectorDatum.hCheck; cbv)
  u b hb hbu := by fin_cases b <;> first | contradiction | (unfold NatSelectorDatum.uCheck; cbv)
  v c hc hcu hcv := by fin_cases c <;> first | contradiction | (unfold NatSelectorDatum.vCheck; cbv)
  terminal := by
    change selector.split.ops.mul
      (terminalRecipe selector.split.ops slotH slotU slotV (naturalParameter 1319) dInv) [461, 942, 371, 590, 264, 2, 182] = [1]
    rw [terminal_eq]
    cbv

end RKCert.GoodPrimeDense.NatRow4
