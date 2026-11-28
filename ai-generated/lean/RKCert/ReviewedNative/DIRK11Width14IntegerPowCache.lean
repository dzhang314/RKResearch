module

public import RKCert.ReviewedNative.DIRK11Width14IntegerPowData
import Mathlib.Tactic.IntervalCases

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000


theorem eqV_identity {u v : V} (ok : eqV u v = true) : u=v :=
  funext fun i => of_decide_eq_true (List.all_eq_true.mp ok i (List.mem_finRange i))

theorem pow_zero_checked : litPow 0 = one := by
  apply eqV_identity
  decide +kernel
theorem pow_at0 : litPow 1 = mulV packet (litPow 0) (node packet) := by
  apply eqV_identity
  decide +kernel
theorem pow_at1 : litPow 2 = mulV packet (litPow 1) (node packet) := by
  apply eqV_identity
  decide +kernel
theorem pow_at2 : litPow 3 = mulV packet (litPow 2) (node packet) := by
  apply eqV_identity
  decide +kernel
theorem pow_at3 : litPow 4 = mulV packet (litPow 3) (node packet) := by
  apply eqV_identity
  decide +kernel
theorem pow_at4 : litPow 5 = mulV packet (litPow 4) (node packet) := by
  apply eqV_identity
  decide +kernel
theorem pow_at5 : litPow 6 = mulV packet (litPow 5) (node packet) := by
  apply eqV_identity
  decide +kernel
theorem pow_at6 : litPow 7 = mulV packet (litPow 6) (node packet) := by
  apply eqV_identity
  decide +kernel
theorem pow_at7 : litPow 8 = mulV packet (litPow 7) (node packet) := by
  apply eqV_identity
  decide +kernel
theorem pow_at8 : litPow 9 = mulV packet (litPow 8) (node packet) := by
  apply eqV_identity
  decide +kernel
theorem pow_at9 : litPow 10 = mulV packet (litPow 9) (node packet) := by
  apply eqV_identity
  decide +kernel

theorem pow_lit_next (d : Nat) (hd : d < 10) :
    litPow (d+1) = mulV packet (litPow d) (node packet) := by
  interval_cases d
  · exact pow_at0
  · exact pow_at1
  · exact pow_at2
  · exact pow_at3
  · exact pow_at4
  · exact pow_at5
  · exact pow_at6
  · exact pow_at7
  · exact pow_at8
  · exact pow_at9

theorem pow_checked (d : Nat) (hd : d ≤ 10) : powC packet d = litPow d := by
  induction d with
  | zero => exact pow_zero_checked.symm
  | succ d ih =>
    have r : powC packet (d+1) = mulV packet (powC packet d) (node packet) := rfl
    rw [r,ih (by omega),←pow_lit_next d (by omega)]

end RKResearch.Certified.DIRK11Width14IntegerChecks
