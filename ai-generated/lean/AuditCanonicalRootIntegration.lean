module

import RKCert.ReviewedNative.CanonicalReducedUniqueness

/-! One unrun root probe. No compilation or axiom output is claimed. -/
open RKResearch RKResearch.CanonicalProfile RKResearch.CanonicalUniqueness
open scoped Classical Matrix

section
variable {K : Type*} [Field K] {s s' p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {B : Matrix (Fin s') (Fin s') K}
variable {b : Fin s → K} {d : Fin s' → K}

-- The chosen finite full-profile quotient and actual visible restriction
-- retain the original reviewed predicate and every literal output.
example (ho : HasOrder p A b) (t : FiniteRootedTree) :
    HasOrder p ((canonicalPartition A).reducedMatrix b) ((canonicalPartition A).reducedWeight b) ∧
      (canonicalPartition A).reducedWeight b ⬝ᵥ Φ t ((canonicalPartition A).reducedMatrix b) =
        b ⬝ᵥ Φ t A :=
  ⟨((canonicalPartition A).reduced_hasOrder_iff b p).mpr ho,
    (canonicalPartition A).reduced_scalar_output b t⟩

-- Two chosen quotients of the same full series give the same literal
-- reduced coefficients up to stage permutation, still at reviewed order p.
example (ho : HasOrder p A b)
    (same : ∀ t : FiniteRootedTree, b ⬝ᵥ Φ t A = d ⬝ᵥ Φ t B) :
    HasOrder p ((canonicalPartition B).reducedMatrix d) ((canonicalPartition B).reducedWeight d) ∧
      ∃ e : (canonicalPartition B).ReducedIndex d ≃ (canonicalPartition A).ReducedIndex b,
        (∀ j k, (canonicalPartition B).reducedMatrix d j k =
          (canonicalPartition A).reducedMatrix b (e j) (e k)) ∧
          ∀ j, (canonicalPartition B).reducedWeight d j = (canonicalPartition A).reducedWeight b (e j) := by
  have hoB : HasOrder p B d := by
    intro t ht
    rw [← same t]
    exact ho t ht
  exact ⟨((canonicalPartition B).reduced_hasOrder_iff d p).mpr hoB,
    reduced_permutation_of_same_series (canonicalPartition A) (canonicalPartition B) b d same⟩

end

#check @RKResearch.CanonicalProfile.Partition.scalar_output
#check @RKResearch.CanonicalVisibility.path_readout
#check @RKResearch.CanonicalVisibility.invisibleIdeal_greatest
#check @RKResearch.CanonicalProfile.Partition.reduced_scalar_output
#check @RKResearch.CanonicalProfile.Partition.reduced_hasOrder_iff
#check @RKResearch.CanonicalUniqueness.reduced_permutation_of_same_series

#print axioms RKResearch.CanonicalProfile.Partition.scalar_output
#print axioms RKResearch.CanonicalVisibility.invisibleIdeal_greatest
#print axioms RKResearch.CanonicalProfile.Partition.reduced_scalar_output
#print axioms RKResearch.CanonicalProfile.Partition.reduced_hasOrder_iff
#print axioms RKResearch.CanonicalUniqueness.reduced_permutation_of_same_series
