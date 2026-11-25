module

public import RKCert.ReviewedNative.TopologicalLastLive

public section

namespace RKResearch.Certified.Topological

example {V B : Type*} [Fintype V] [LinearOrder B] {n : ℕ}
    (hcard : Fintype.card V = n) (R : V → V → Prop)
    (old : V ↪ B) (hold : RespectsEdges R old) (t : V) :
    ∃ σ : V ≃ Fin n, RespectsEdges R σ ∧
      ∀ u, σ t < σ u ↔ Relation.TransGen R t u :=
  exists_rank_exact_strict_suffix hcard R old hold t

example {V : Type*} [Fintype V] {n : ℕ}
    (R : V → V → Prop) (live : V → Prop) (t : V) :
    (∃ σ : V ≃ Fin n, RespectsEdges R σ ∧ live t ∧
      ∀ u, σ t < σ u → ¬ live u) ↔
    (∃ σ : V ≃ Fin n, RespectsEdges R σ) ∧ live t ∧
      ∀ u, Relation.TransGen R t u → ¬ live u :=
  exists_last_live_rank_iff (n := n) R live t

#print axioms exists_rank_exact_strict_suffix
#print axioms exists_last_live_rank_iff

end RKResearch.Certified.Topological
