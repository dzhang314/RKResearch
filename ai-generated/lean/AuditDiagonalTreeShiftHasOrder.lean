module

import RKCert.ReviewedNative.DiagonalTreeShiftHasOrder

/-! Typed clients for the exact-flow normalization and both shift transports. -/
open RKResearch RKResearch.DiagonalTreeShift
open scoped Matrix

section

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

example (t : FiniteRootedTree) :
    exactFlowOutput K t = (t.factorial : K)⁻¹ := rfl

example [CharZero K] (p : ℕ) (B : Matrix ι ι K) (b : ι → K) (γ : K) :
    RKResearch.HasOrder p (B + γ • (1 : Matrix ι ι K)) b ↔
      ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ p →
        b ⬝ᵥ Φ t B = transform K (-γ) (fun u => (u.factorial : K)⁻¹) t :=
  hasOrder_add_diagonal_iff p B b γ

example (n : ℕ) (B : Matrix ι ι K) (b : ι → K) (γ : K) :
    FirstDifferenceAt n (fun t => b ⬝ᵥ Φ t (B + γ • (1 : Matrix ι ι K)))
      (fun t => (t.factorial : K)⁻¹) ↔
      FirstDifferenceAt n (fun t => b ⬝ᵥ Φ t B) (transform K (-γ) (fun t => (t.factorial : K)⁻¹)) :=
  firstDifference_add_diagonal_iff n B b γ

end

#check @RKResearch.DiagonalTreeShift.exactFlowOutput
#check @RKResearch.DiagonalTreeShift.hasOrder_add_diagonal_iff
#check @RKResearch.DiagonalTreeShift.firstDifference_add_diagonal_iff

#print axioms RKResearch.DiagonalTreeShift.hasOrder_add_diagonal_iff
#print axioms RKResearch.DiagonalTreeShift.firstDifference_add_diagonal_iff
