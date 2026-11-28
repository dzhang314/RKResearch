module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

/-! # Finite clock coverage by the nonzero norm numerators and denominators -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicLiveFinite

open Polynomial

/-- The finite-norm cover implication used after proving the guard and
test norms are nonzero. The specialization certificate itself is
separate from this set-theoretic gate. -/
theorem finite_of_nonzero_norm_cover {K ι : Type*} [Field K] [Finite ι]
    (S : Set K) (norm : ι → K[X])
    (live : ∀ i, norm i ≠ 0)
    (cover : ∀ x ∈ S, ∃ i, aeval x (norm i) = 0) : S.Finite := by
  have rootsFinite : (⋃ i, (norm i).rootSet K).Finite :=
    Set.finite_iUnion fun i => (norm i).rootSet_finite K
  refine rootsFinite.subset ?_
  intro x hx
  obtain ⟨i,hi⟩ := cover x hx
  exact Set.mem_iUnion.mpr ⟨i,(mem_rootSet_of_ne (live i)).mpr hi⟩

end RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicLiveFinite
