module

public import RKCert.ReviewedNative.CanonicalSplitUniqueness
public import RKCert.ReviewedNative.CanonicalProfilePrune

@[expose] public section

namespace RKResearch.CanonicalUniqueness

open RKResearch RKResearch.CanonicalVisibility RKResearch.CanonicalProfile
open scoped Classical Matrix

noncomputable section
variable {ι K : Type*} [Fintype ι] [Field K]

/-- Principal restriction of an already full tree span is still full.
The proof uses arbitrary zero extensions and literal tree-column transport. -/
theorem pruned_treeSpan_top (A : Matrix ι ι K) (b : ι → K) (full : treeSpan A = ⊤) :
    treeSpan (prunedMatrix A b) = ⊤ := by
  let L : (ι → K) →ₗ[K] (VisibleIndex A b → K) :=
    { toFun := pruneRestrict A b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have closed : treeSpan A ≤ (treeSpan (prunedMatrix A b)).comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    change pruneRestrict A b (Φ t A) ∈ treeSpan (prunedMatrix A b)
    rw [← Φ_pruned]
    exact Submodule.subset_span ⟨t,rfl⟩
  apply top_unique
  intro x _
  let lift : ι → K := fun i => if hi : i ∈ visibleSet A b then x ⟨i,hi⟩ else 0
  have restrict : L lift = x := by
    funext i
    change (if hi : i.val ∈ visibleSet A b then x ⟨i.val,hi⟩ else 0) = x i
    rw [dif_pos i.property]
  have hin : lift ∈ treeSpan A := by rw [full]; trivial
  have h := closed hin
  change L lift ∈ treeSpan (prunedMatrix A b) at h
  simpa only [restrict] using h

variable {s n s' n' : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {B : Matrix (Fin s') (Fin s') K}

/-- Any exact profile-label enumeration followed by visible pruning gives
the same reduced tableau up to permutation of the actual surviving labels. -/
theorem reduced_permutation_of_same_series (P : Partition A n) (Q : Partition B n')
    (b : Fin s → K) (d : Fin s' → K)
    (same : ∀ t : FiniteRootedTree, b ⬝ᵥ Φ t A = d ⬝ᵥ Φ t B) :
    ∃ e : Q.ReducedIndex d ≃ P.ReducedIndex b,
      (∀ j k, Q.reducedMatrix d j k = P.reducedMatrix b (e j) (e k)) ∧
        ∀ j, Q.reducedWeight d j = P.reducedWeight b (e j) := by
  refine permutation_of_same_series (P.reducedMatrix b) (Q.reducedMatrix d)
    (P.reducedWeight b) (Q.reducedWeight d) ?_ ?_ ?_
    (P.reduced_invisible_eq_bot b) (Q.reduced_invisible_eq_bot d)
  · intro t
    exact (P.reduced_scalar_output b t).trans ((same t).trans (Q.reduced_scalar_output d t).symm)
  · exact pruned_treeSpan_top P.aggregateMatrix (P.aggregateWeight b) P.aggregate_reachable_top
  · exact pruned_treeSpan_top Q.aggregateMatrix (Q.aggregateWeight d) Q.aggregate_reachable_top

end
end RKResearch.CanonicalUniqueness
