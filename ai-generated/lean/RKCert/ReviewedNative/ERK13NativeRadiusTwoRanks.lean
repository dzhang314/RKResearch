module

public import RKCert.ReviewedNative.ERK13NativePaidFrame
public import RKCert.ReviewedNative.ERK13NativeMarkedLowProfile
import RKCert.ReviewedNative.ForwardNodalGain
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Radius two alone determines the actual F4 rank

The measured two-peel lemma already places F3 in the core. If F4 had
rank three it would equal that core, violating the native incoming clock
gain. Neither terminal timing, seed, nor square purity is required. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w : Fin 19 → K}
set_option maxHeartbeats 900000

theorem single_span_rank_cap (V : Submodule K (Fin 19 → K)) (z : Fin 19 → K) :
    finrank K (↥(V⊔K∙z : Submodule K (Fin 19 → K)))≤finrank K V+1 := by
  by_cases hz : z∈V
  · rw [sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem ..).mpr hz)]
    omega
  · exact (Submodule.finrank_sup_span_singleton hz).le

/-- Once actual F3 lies in the invariant core, no terminal assumption is
needed for the remaining forward counting step. -/
theorem rank_radius_of_three_in_core {r : ℕ}
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (H : NativePaidHead A b r U w) (inside : zeroSpace A 3≤U) :
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

theorem radius_two_rank_four (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (H : NativePaidHead A b 2 U w) : finrank K (zeroSpace A 4)=4 :=
  (rank_radius_of_three_in_core ha ho H (fun _ hx => radius_two_grade_three_core H hx)).1

end
end RKResearch.Certified.Graded.ERK13NativeFirst
