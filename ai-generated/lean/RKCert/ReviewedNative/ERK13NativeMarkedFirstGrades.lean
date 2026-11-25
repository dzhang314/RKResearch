module

public import RKCert.ReviewedNative.ERK13NativeMarkedLobattoGradeThree
public import RKCert.ReviewedNative.ForwardNodalGain
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Paid low grades after a genuine grade-three core cut

The rank argument needs neither the ordinary staircase nor a choice of
terminal time. Its only new premise is a proved grade-three inclusion.
The degree-six first-escape corollary supplies that inclusion outright. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}
variable {G : K[X]} {U : Submodule K (Fin 19→K)} {w : Fin 19→K} {r : ℕ}

theorem NativePaidHead.first_grades_of_three_le_core
    (H : NativePaidHead A b r U w)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (inside : zeroSpace A 3 ≤ U) :
    finrank K (zeroSpace A 4)=4 ∧ (r=2 ∨ r=3) ∧
      (r=3 → zeroSpace A 3=U ∧ finrank K U=2) := by
  have sep := coeff_separated ho (q:=6) (by decide)
  have lo3 := zeroSpace_rank_interval_of_separation (j:=1) (d:=2)
    ha sep (by decide) (by decide)
  have grow34 := zeroSpace_rank_interval_of_separation (j:=3) (d:=1)
    ha sep (by decide) (by decide)
  have grow45 := zeroSpace_rank_interval_of_separation (j:=4) (d:=1)
    ha sep (by decide) (by decide)
  change finrank K (zeroSpace A 1)+2≤finrank K (zeroSpace A 3) at lo3
  change finrank K (zeroSpace A 3)+1≤finrank K (zeroSpace A 4) at grow34
  change finrank K (zeroSpace A 4)+1≤finrank K (zeroSpace A 5) at grow45
  rw [H.five] at grow45
  have lowU := Submodule.finrank_mono inside
  have rU := H.head.baseRank
  rw [H.five] at rU
  have rlo := H.headBounds.1
  have stable := H.head.coreStable
  have r4 : finrank K (zeroSpace A 4)=4 := by
    by_contra neq
    have f3 : finrank K (zeroSpace A 3)=2 := by omega
    have f4 : finrank K (zeroSpace A 4)=3 := by omega
    have esc : ¬(zeroSpace A 3).map (diag (nodes A))≤zeroSpace A 3 := by
      intro h
      have gain := clock_invariant_outgoing (j:=3) ha
        ((PolySeparated.of_coeff sep).mono (by decide)) le_rfl h
      change finrank K (zeroSpace A 3)+2≤finrank K (zeroSpace A 4) at gain
      omega
    have eq := zeroSpace_clock_step_of_unit (n:=3)
      (show finrank K (zeroSpace A 4)≤finrank K (zeroSpace A 3)+1 by omega) esc
    have inc : zeroSpace A 4≤U := by
      rw [eq]
      exact sup_le inside ((Submodule.map_mono inside).trans stable)
    have full : zeroSpace A 4=U :=
      Submodule.eq_of_le_of_finrank_le inc (by omega)
    have invariant : (zeroSpace A 4).map (diag (nodes A))≤zeroSpace A 4 := by
      simpa only [full] using stable
    have gain := clock_invariant_incoming (j:=3) ha
      ((PolySeparated.of_coeff sep).mono (by decide)) invariant
    change finrank K (zeroSpace A 3)+2≤finrank K (zeroSpace A 4) at gain
    omega
  refine ⟨r4,by omega,fun hr=>⟨Submodule.eq_of_le_of_finrank_le inside (by omega),by omega⟩⟩

theorem NativeMarkedEscapeChart.first_grades_of_degree_six
    (H : NativeMarkedEscapeChart A b 5 G r U w)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    finrank K (zeroSpace A 4)=4 ∧ (r=2 ∨ r=3) ∧
      (r=3 → zeroSpace A 3=U ∧ finrank K U=2) :=
  H.head.first_grades_of_three_le_core ha ho (H.grade_three_le_core_of_degree_six ha ho)

end
end RKResearch.Certified.Graded.ERK13NativeFirst
