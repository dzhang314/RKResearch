module

import RKCert.ReviewedNative.CanonicalProfileCoalesce

/-! Typed clients for full-profile aggregation only. -/
open RKResearch RKResearch.CanonicalProfile RKResearch.Certified.Graded
open scoped BigOperators Classical Matrix

section
variable {K : Type*} [Field K] {s n p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

example (i j : Fin s) :
    (canonicalPartition A).label i = (canonicalPartition A).label j ↔
      ∀ t : FiniteRootedTree, Φ t A i = Φ t A j :=
  (canonicalPartition A).label_eq_iff i j

example (P : Partition A n) (v : Fin s → K) :
    v ∈ reachable A ↔ ∀ i j, P.label i = P.label j → v i = v j :=
  P.mem_reachable_iff v

-- The actual full tree span has exactly one independent coordinate per class.
example (P : Partition A n) : Module.finrank K (reachable A) = n := by
  let e : (Fin n → K) ≃ₗ[K] reachable A :=
    { toFun := fun f => ⟨fun i => f (P.label i),
        (P.mem_reachable_iff _).mpr (fun _ _ same => congrArg f same)⟩
      invFun := fun v a => v.val (P.rep a)
      left_inv := by
        intro f
        funext a
        exact congrArg f (P.label_rep a)
      right_inv := by
        intro v
        apply Subtype.ext
        funext i
        exact P.agree_of_mem v.property (P.label_rep (P.label i))
      map_add' := by intro f g; rfl
      map_smul' := by intro c f; rfl }
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using e.finrank_eq.symm

example (P : Partition A n) (i j : Fin s) (same : P.label i = P.label j) (a : Fin n) :
    (∑ k ∈ Finset.univ.filter (fun k => P.label k = a), A i k) =
      ∑ k ∈ Finset.univ.filter (fun k => P.label k = a), A j k :=
  P.sum_into_class_eq same a

example (P : Partition A n) (i : Fin s) (a : Fin n) :
    P.aggregateMatrix (P.label i) a =
      ∑ j ∈ Finset.univ.filter (fun j => P.label j = a), A i j :=
  P.aggregateMatrix_value i a

example (P : Partition A n) (t : FiniteRootedTree) (i : Fin s) :
    Φ t P.aggregateMatrix (P.label i) = Φ t A i :=
  P.Φ_pullback t i

example (t : FiniteRootedTree) :
    (canonicalPartition A).aggregateWeight b ⬝ᵥ Φ t (canonicalPartition A).aggregateMatrix =
      b ⬝ᵥ Φ t A :=
  (canonicalPartition A).scalar_output b t

example :
    HasOrder p (canonicalPartition A).aggregateMatrix ((canonicalPartition A).aggregateWeight b) ↔
      HasOrder p A b :=
  (canonicalPartition A).hasOrder_iff b p

end

#check @RKResearch.CanonicalProfile.canonicalPartition
#check @RKResearch.CanonicalProfile.Partition.mem_reachable_iff
#check @RKResearch.CanonicalProfile.Partition.indicator_mem
#check @RKResearch.CanonicalProfile.Partition.sum_into_class_eq
#check @RKResearch.CanonicalProfile.Partition.aggregateMatrix_value
#check @RKResearch.CanonicalProfile.Partition.Φ_pullback
#check @RKResearch.CanonicalProfile.Partition.scalar_output
#check @RKResearch.CanonicalProfile.Partition.hasOrder_iff

#print axioms RKResearch.CanonicalProfile.canonicalPartition
#print axioms RKResearch.CanonicalProfile.Partition.mem_reachable_iff
#print axioms RKResearch.CanonicalProfile.Partition.indicator_mem
#print axioms RKResearch.CanonicalProfile.Partition.sum_into_class_eq
#print axioms RKResearch.CanonicalProfile.Partition.aggregateMatrix_value
#print axioms RKResearch.CanonicalProfile.Partition.Φ_pullback
#print axioms RKResearch.CanonicalProfile.Partition.scalar_output
#print axioms RKResearch.CanonicalProfile.Partition.hasOrder_iff
