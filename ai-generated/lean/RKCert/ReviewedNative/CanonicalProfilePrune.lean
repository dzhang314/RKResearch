module

public import RKCert.ReviewedNative.CanonicalProfileCoalesce
public import RKCert.ReviewedNative.CanonicalVisiblePrune

@[expose] public section

/-! The actual profile merge followed by the visible principal restriction.
This adapter does not invoke a free-tree model or a uniqueness theorem. -/
namespace RKResearch.CanonicalProfile.Partition

open RKResearch RKResearch.CanonicalProfile RKResearch.CanonicalVisibility
open scoped Classical Matrix

noncomputable section
variable {K : Type*} [Field K] {s n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} (P : Partition A n)

private theorem aggregate_profile_injective {i j : Fin n}
    (same : ∀ t : FiniteRootedTree, Φ t P.aggregateMatrix i = Φ t P.aggregateMatrix j) : i=j := by
  have h : P.label (P.rep i) = P.label (P.rep j) := (P.label_eq_iff _ _).mpr (fun t => by
    simpa only [P.Φ_aggregate t] using same t)
  simpa only [P.label_rep] using h

/-- This discharges the domain qualification of split observability:
all coordinate multipliers of the coalesced tableau are reachable. -/
theorem aggregate_reachable_top : reachable P.aggregateMatrix = ⊤ := by
  let Q : Partition P.aggregateMatrix n :=
    ⟨id, id, fun _ => rfl, fun i j => by
      constructor
      · rintro rfl t
        rfl
      · exact P.aggregate_profile_injective⟩
  apply top_unique
  intro v _
  apply (Q.mem_reachable_iff v).mpr
  intro i j same
  exact congrArg v same

abbrev ReducedIndex (b : Fin s → K) := VisibleIndex P.aggregateMatrix (P.aggregateWeight b)

abbrev reducedMatrix (b : Fin s → K) : Matrix (P.ReducedIndex b) (P.ReducedIndex b) K :=
  prunedMatrix P.aggregateMatrix (P.aggregateWeight b)

abbrev reducedWeight (b : Fin s → K) : P.ReducedIndex b → K :=
  prunedWeight P.aggregateMatrix (P.aggregateWeight b)

theorem reduced_scalar_output (b : Fin s → K) (t : FiniteRootedTree) :
    P.reducedWeight b ⬝ᵥ Φ t (P.reducedMatrix b) = b ⬝ᵥ Φ t A :=
  (pruned_scalar_output P.aggregateMatrix (P.aggregateWeight b) t).trans (P.scalar_output b t)

theorem reduced_hasOrder_iff (b : Fin s → K) (p : ℕ) :
    HasOrder p (P.reducedMatrix b) (P.reducedWeight b) ↔ HasOrder p A b :=
  (pruned_hasOrder_iff P.aggregateMatrix (P.aggregateWeight b) p).trans (P.hasOrder_iff b p)

theorem reduced_invisible_eq_bot (b : Fin s → K) :
    invisible (P.reducedMatrix b) (P.reducedWeight b) = ⊥ :=
  invisible_pruned_eq_bot P.aggregateMatrix (P.aggregateWeight b)

end
end RKResearch.CanonicalProfile.Partition
