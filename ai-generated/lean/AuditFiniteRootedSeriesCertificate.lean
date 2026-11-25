module

import RKCert.ReviewedNative.FiniteRootedSeriesCertificate

/-! Typed warm probes for the source-only finite comparison certificate. -/
open RKResearch RKResearch.FiniteSeries RKResearch.Certified.Graded
open scoped Matrix FiniteRootedTree

section
variable {ι R : Type*} [Fintype ι] [CommSemiring R]
variable {A : Matrix ι ι R} {b : ι → R}
variable {marks : List FiniteRootedTree} {cut g cap : ℕ}

example (closed : ClosedBelow A marks cut) (pay : g < cut) :
    markSpan A marks g = treeSpace A g :=
  markSpan_eq_treeSpace A marks closed pay

example (closed : ClosedBelow A marks cut)
    (zero : ∀ u ∈ marks, treeGrade u < cut → b ⬝ᵥ Φ u A = 0)
    (t : FiniteRootedTree) (pay : (t.order : ℕ) ≤ cut) : b ⬝ᵥ Φ t A = 0 := by
  have gradePay : treeGrade t + 1 ≤ cut := (treeGrade_succ t).trans_le pay
  exact series_zero_below A marks closed b zero t (Nat.lt_of_succ_le gradePay)

example (t : FiniteRootedTree) (closed : ClosedBelow A marks (treeGrade t))
    (nz : b ⬝ᵥ Φ t A ≠ 0)
    (zero : ∀ u ∈ marks, treeGrade u < treeGrade t → b ⬝ᵥ Φ u A = 0) :
    (b ⬝ᵥ Φ t A ≠ 0) ∧
      ∀ u : FiniteRootedTree, b ⬝ᵥ Φ u A ≠ 0 → (t.order : ℕ) ≤ (u.order : ℕ) :=
  least_distinguishing_order A marks b t closed nz zero

-- At a nonzero leaf there is no previous grade to certify, even with no marks.
example (nz : b ⬝ᵥ Φ .leaf A ≠ 0) :
    ∀ u : FiniteRootedTree, b ⬝ᵥ Φ u A ≠ 0 → ((FiniteRootedTree.leaf).order : ℕ) ≤ (u.order : ℕ) := by
  have closed : ClosedBelow A [] (treeGrade .leaf) := by
    refine ⟨?_, ?_, ?_⟩
    · intro dead
      exact (Nat.lt_irrefl 0 dead).elim
    · intro _ none
      exact (List.not_mem_nil none).elim
    · intro _ none
      exact (List.not_mem_nil none).elim
  exact (least_distinguishing_order A [] b .leaf closed nz
    (fun _ none _ => (List.not_mem_nil none).elim)).2

example (closed : ClosedBelow A marks (2 * cap + 2))
    (bound : ∀ t ∈ marks, treeGrade t ≤ cap)
    (zero : ∀ t ∈ marks, b ⬝ᵥ Φ t A = 0) :
    ∀ t : FiniteRootedTree, b ⬝ᵥ Φ t A = 0 :=
  (full_series_zero_iff_checked_marks A marks b closed bound).mpr zero

end

#check @RKResearch.FiniteSeries.ClosedBelow
#check @RKResearch.FiniteSeries.treeGrade_rootedSum
#check @RKResearch.FiniteSeries.markSpan_eq_treeSpace
#check @RKResearch.FiniteSeries.series_zero_below
#check @RKResearch.FiniteSeries.least_distinguishing_order
#check @RKResearch.FiniteSeries.full_series_zero_iff_checked_marks

#print axioms RKResearch.FiniteSeries.markSpan_eq_treeSpace
#print axioms RKResearch.FiniteSeries.series_zero_below
#print axioms RKResearch.FiniteSeries.least_distinguishing_order
#print axioms RKResearch.FiniteSeries.full_series_zero_iff_checked_marks
