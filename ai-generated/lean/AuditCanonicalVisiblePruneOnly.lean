module

import RKCert.ReviewedNative.CanonicalVisiblePrune

/-! A narrow typed audit of the checked visibility and pruning body.
Nothing depends on a coalescing adapter or a uniqueness theorem. -/
open RKResearch RKResearch.CanonicalVisibility RKResearch.Certified.Graded
open RKResearch.Certified.Graded.Reverse
open scoped Classical Matrix

section
variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

-- An actual edge into a weighted recipient suffices, without any
-- hypothesis on the individual output weight of the input stage.
example {i j : Fin s} (edge : A j i ≠ 0) (live : b j ≠ 0) :
    ∃ C : Context (Fin s) K, ∃ a : K, a ≠ 0 ∧
      ∀ v : Fin s → K, b ⬝ᵥ C.eval A v = a*v i := by
  have hit : Visible A b i := Visible.step (j:=j) edge (Visible.output j live)
  simpa only [row_apply] using path_readout A b hit

example (v : Fin s → K) :
    v ∈ invisibleIdeal A b ↔ ∀ i, Visible A b i → v i = 0 :=
  mem_invisibleIdeal_iff A b

example :
    IsGreatest {J : Ideal (Fin s → K) |
      (∀ v ∈ J, A *ᵥ v ∈ J) ∧ (∀ v ∈ J, b ⬝ᵥ v = 0)} (invisibleIdeal A b) := by
  simpa only [mat_apply, row_apply] using invisibleIdeal_greatest A b

example (t : FiniteRootedTree) (i : VisibleIndex A b) :
    Φ t (prunedMatrix A b) i = Φ t A i.val :=
  congrFun (Φ_pruned A b t) i

example (ho : HasOrder p A b) (t : FiniteRootedTree) :
    HasOrder p (prunedMatrix A b) (prunedWeight A b) ∧
      prunedWeight A b ⬝ᵥ Φ t (prunedMatrix A b) = b ⬝ᵥ Φ t A :=
  ⟨(pruned_hasOrder_iff A b p).mpr ho, pruned_scalar_output A b t⟩

example (i : VisibleIndex A b) :
    Visible (prunedMatrix A b) (prunedWeight A b) i :=
  visible_pruned A b i

example : invisible (prunedMatrix A b) (prunedWeight A b) = ⊥ :=
  invisible_pruned_eq_bot A b

end

#check @RKResearch.CanonicalVisibility.path_readout
#check @RKResearch.CanonicalVisibility.mem_invisibleIdeal_iff
#check @RKResearch.CanonicalVisibility.invisibleIdeal_greatest
#check @RKResearch.CanonicalVisibility.Φ_pruned
#check @RKResearch.CanonicalVisibility.pruned_scalar_output
#check @RKResearch.CanonicalVisibility.pruned_hasOrder_iff
#check @RKResearch.CanonicalVisibility.visible_pruned
#check @RKResearch.CanonicalVisibility.invisible_pruned_eq_bot

#print axioms RKResearch.CanonicalVisibility.path_readout
#print axioms RKResearch.CanonicalVisibility.mem_invisibleIdeal_iff
#print axioms RKResearch.CanonicalVisibility.invisibleIdeal_greatest
#print axioms RKResearch.CanonicalVisibility.Φ_pruned
#print axioms RKResearch.CanonicalVisibility.pruned_scalar_output
#print axioms RKResearch.CanonicalVisibility.pruned_hasOrder_iff
#print axioms RKResearch.CanonicalVisibility.visible_pruned
#print axioms RKResearch.CanonicalVisibility.invisible_pruned_eq_bot
