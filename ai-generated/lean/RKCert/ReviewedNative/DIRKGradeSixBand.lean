module

public import RKCert.ReviewedNative.DIRKPrefixHermite
public import RKCert.ReviewedNative.DIRKForwardRank

@[expose] public section

/-! # Native reduction of a failed grade-six surplus
Strict two-seed increases would then consume the entire three-step budget.
The inclusive Hermite inequalities exclude clock invariance at *each* of
the three higher grades, including the final grade by an incoming test. -/
namespace RKResearch.Certified.Graded

open Module
open scoped Matrix
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- The unit band and its three obligatory clock escapes. Grade seven
already pays every probe in this reduction. This alone does not exclude
the two possible starts of the remaining one-head chart. -/
theorem dirk_unit_band_of_no_grade_six_surplus (ha : A.IsLowerTriangular)
    (ho : HasOrder p A b) (pay : 7≤p)
    (bad : ¬finrank K (zeroSpace A 3)+4≤finrank K (zeroSpace A 6)) :
    (∀ j, 3≤j → j<6 → finrank K (zeroSpace A (j+1)) = finrank K (zeroSpace A j)+1) ∧
    (∀ j, 4≤j → j≤6 → ¬(zeroSpace A j).map (diag (nodes A)) ≤ zeroSpace A j) := by
  have grow (j : ℕ) (lo : 3≤j) (hi : j<6) :
      finrank K (zeroSpace A j)<finrank K (zeroSpace A (j+1)) :=
    Submodule.finrank_lt_finrank_of_lt (dirk_forward_zeroSpace_lt_succ ha ho (by omega) (by omega))
  have g34 := grow 3 (by decide) (by decide)
  have g45 := grow 4 (by decide) (by decide)
  have g56 := grow 5 (by decide) (by decide)
  simp only [Nat.reduceAdd] at g34 g45 g56
  have exactStep (j : ℕ) (lo : 3≤j) (hi : j<6) :
      finrank K (zeroSpace A (j+1)) = finrank K (zeroSpace A j)+1 := by
    rcases (show j=3 ∨ j=4 ∨ j=5 by omega) with rfl|rfl|rfl <;> simp only [Nat.reduceAdd] <;> omega
  refine ⟨exactStep,?_⟩
  intro j lo hi inv
  have closed (v) (hv : v∈zeroSpace A j) : diag (nodes A) v∈zeroSpace A j :=
    inv (Submodule.mem_map_of_mem hv)
  by_cases last : j=6
  · subst j
    have gain := dirk_forward_invariant_incoming ha ho (j:=5) pay closed
    have eq := exactStep 5 (by decide) (by decide)
    omega
  · have gain := dirk_forward_invariant_outgoing ha ho (by omega) (zeroSpace A j) le_rfl closed
    have eq := exactStep j (by omega) (by omega)
    omega

/-- Clock invariance of any one of F4, F5, F6 is enough for the genuine
extra dimension. No assumption about the F3 clock action is needed. -/
theorem dirk_grade_six_surplus_of_invariant_grade (ha : A.IsLowerTriangular)
    (ho : HasOrder p A b) (pay : 7≤p) {j : ℕ} (lo : 4≤j) (hi : j≤6)
    (inv : (zeroSpace A j).map (diag (nodes A)) ≤ zeroSpace A j) :
    finrank K (zeroSpace A 3)+4≤finrank K (zeroSpace A 6) := by
  by_contra bad
  exact (dirk_unit_band_of_no_grade_six_surplus ha ho pay bad).2 j lo hi inv

end RKResearch.Certified.Graded
