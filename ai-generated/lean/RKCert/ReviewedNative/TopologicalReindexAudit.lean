module

public import RKCert.ReviewedNative.TopologicalReindex

public section

namespace RKResearch.Certified.Topological

open RKResearch.Certified.Graded.Reverse (LastActive)

example {V K : Type*} [Zero K] {n : ℕ}
    (A : Matrix V V K) (σ : V ≃ Fin n) :
    (∀ i j, i ≤ j → (Matrix.reindex σ σ A) i j = 0) ↔
      RespectsEdges (fun u v => A v u ≠ 0) σ :=
  reindex_strict_iff_respectsEdges A σ

example {V K : Type*} [Field K] {n : ℕ}
    (b : V → K) (σ : V ≃ Fin n) (t : V) :
    LastActive (b ∘ σ.symm) (σ t) ↔
      b t ≠ 0 ∧ ∀ u, σ t < σ u → b u = 0 :=
  reindexed_lastActive_iff b σ t

#print axioms reindex_strict_iff_respectsEdges
#print axioms reindexed_lastActive_iff

end RKResearch.Certified.Topological
