module

public import RKCert.ReviewedNative.TopologicalLastLive
public import RKCert.ReviewedNative.EndpointAdjoint

@[expose] public section

/-! # Actual topological reindexing

The reindexed matrix uses the inverse permutation on both coordinates.
Strict lower triangularity consequently tests the direction of every
nonzero input edge. Separately, the reindexed last-active predicate
tests the original weights in the new chronology.
-/
namespace RKResearch.Certified.Topological

open RKResearch.Certified.Graded.Reverse (LastActive)

/-- Reindexing by a rank gives a strictly lower triangular matrix
exactly when every nonzero entry points from an earlier column
to a later row. -/
theorem reindex_strict_iff_respectsEdges {V K : Type*} [Zero K] {n : ℕ}
    (A : Matrix V V K) (σ : V ≃ Fin n) :
    (∀ i j, i ≤ j → (Matrix.reindex σ σ A) i j = 0) ↔
      RespectsEdges (fun u v => A v u ≠ 0) σ := by
  constructor
  · intro h u v edge
    apply lt_of_not_ge
    intro hge
    apply edge
    simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
      using h (σ v) (σ u) hge
  · intro h i j hij
    apply Classical.byContradiction
    intro nz
    have edge : A (σ.symm i) (σ.symm j) ≠ 0 := by
      simpa only [Matrix.reindex_apply, Matrix.submatrix_apply] using nz
    have hlt : σ (σ.symm j) < σ (σ.symm i) := h edge
    have hji : j < i := by simpa only [Equiv.apply_symm_apply] using hlt
    exact (not_lt_of_ge hij) hji

/-- Last activity for the inverse-reindexed weights is the literal
support condition measured in the new rank. -/
theorem reindexed_lastActive_iff {V K : Type*} [Field K] {n : ℕ}
    (b : V → K) (σ : V ≃ Fin n) (t : V) :
    LastActive (b ∘ σ.symm) (σ t) ↔
      b t ≠ 0 ∧ ∀ u, σ t < σ u → b u = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply] using h.live
    · intro u hu
      simpa only [Function.comp_apply, Equiv.symm_apply_apply] using h.after (σ u) hu
  · intro h
    rcases h with ⟨ht, ha⟩
    refine ⟨?_, ?_⟩
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply] using ht
    · intro i hi
      have hi' : σ t < σ (σ.symm i) := by
        simpa only [Equiv.apply_symm_apply] using hi
      exact ha (σ.symm i) hi'

end RKResearch.Certified.Topological
