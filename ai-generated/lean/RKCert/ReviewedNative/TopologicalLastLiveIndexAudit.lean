module

public import RKCert.ReviewedNative.TopologicalLastLiveIndex

public section

namespace RKResearch.Certified.Topological

example {V : Type*} [Fintype V] {n : ℕ}
    (R : V → V → Prop) (old : V ≃ Fin n) (hold : RespectsEdges R old)
    (t : V) (E : Finset V) :
    (∃ σ : V ≃ Fin n, RespectsEdges R σ ∧ ∀ u, σ u < σ t ↔ u ∈ E) ↔
      t ∉ E ∧ (∀ ⦃a b⦄, R a b → b ∈ E → a ∈ E) ∧
        ∀ ⦃a⦄, R a t → a ∈ E :=
  exists_rank_exact_prefix_iff R old hold t E

example {V : Type*} [Fintype V] {n : ℕ}
    (R : V → V → Prop) (live : V → Prop) (old : V ≃ Fin n)
    (hold : RespectsEdges R old) (hne : ∃ t, live t) :
    IsLeast {k : ℕ | ∃ (σ : V ≃ Fin n) (t : V), RespectsEdges R σ ∧ live t ∧
      (∀ u, σ t < σ u → ¬ live u) ∧ (σ t).val = k}
      ((liveAncestors R live).card - 1) :=
  isLeast_last_live_index R live old hold hne

#print axioms exists_rank_exact_prefix_iff
#print axioms isLeast_last_live_index

end RKResearch.Certified.Topological
