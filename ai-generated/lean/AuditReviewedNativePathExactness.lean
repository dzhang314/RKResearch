module

import RKCert.ReviewedNative.PathExactnessCorrection

open RKResearch RKResearch.Certified.PathExactness
open scoped Matrix

section
variable {R : Type*} [CommRing R]

-- The correction kills every native tree read in the paid band.
example (γ : R) (n : ℕ) (t : FiniteRootedTree) (paid : (t.order : ℕ) ≤ n + 1) :
    (pathCorrection n : Fin (n + 2) → R) ⬝ᵥ Φ t (adjacentPath γ (n + 1)) = 0 :=
  pathCorrection_paid γ n t paid

-- The literal next tall tree has raw response one, not a normalized response.
example (γ : R) (n : ℕ) :
    (pathCorrection n : Fin (n + 2) → R) ⬝ᵥ
      Φ (FiniteRootedTree.tallTree (n + 1).succPNat) (adjacentPath γ (n + 1)) = 1 :=
  pathCorrection_next_tall γ n

-- The exact transfer is in native HasOrder, at the same A with the literal new row.
example {ι : Type*} [Fintype ι] [Nontrivial R] (n : ℕ)
    (A : Matrix ι ι R) (b d : ι → R) (base : HasOrder (n + 1) A b)
    (paid : ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ n + 1 → d ⬝ᵥ Φ t A = 0)
    (next : d ⬝ᵥ Φ (FiniteRootedTree.tallTree (n + 1).succPNat) A = 1) :
    HasOrder (n + 1) A (b - (b ⬝ᵥ Φ (FiniteRootedTree.tallTree (n + 1).succPNat) A) • d) ∧
      ¬ HasOrder (n + 2) A (b - (b ⬝ᵥ Φ (FiniteRootedTree.tallTree (n + 1).succPNat) A) • d) :=
  exact_order_of_next_tall_correction (n := n) base paid next

end

#print axioms RKResearch.Certified.PathExactness.pathCorrection_paid
#print axioms RKResearch.Certified.PathExactness.pathCorrection_next_tall
#print axioms RKResearch.Certified.PathExactness.exact_order_of_next_tall_correction
