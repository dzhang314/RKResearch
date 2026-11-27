import RKCert.ReviewedNative.MovablePurePort

open RKResearch RKResearch.Certified.TwoDonorDense
open scoped Matrix FiniteRootedTree

example {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
    {A : Matrix ι ι K} {q : ℕ} {D : Matrix (Fin (q+1)) ι K}
    (hD : IsDecoder A q D) (x γ : K) (h : ι → K) (hq : 1 ≤ q)
    (hn : ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ q → h ⬝ᵥ normalized A t = 0)
    (t u : FiniteRootedTree) (ht : ((t ◂ u).order : ℕ) ≤ q+2) :
    normalized (appendStage A (pureFeed D x γ+h) γ) (t ◂ u) (Sum.inr PUnit.unit) =
      x^(((t ◂ u).order : ℕ)-1) +
        (if (u.order : ℕ) ≤ q then 0 else (u.order : K)*(h ⬝ᵥ normalized A u)) :=
  null_perturbation_firstExcess hD x γ h hq hn t u ht

#print axioms null_perturbation_firstExcess
