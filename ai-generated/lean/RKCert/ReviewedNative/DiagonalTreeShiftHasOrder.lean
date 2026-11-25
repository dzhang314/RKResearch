module

public import RKCert.ReviewedNative.DiagonalTreeShiftMatrix
public import RKCert.ReviewedNative.DiagonalTreeShiftOrder
public import Mathlib.Algebra.CharZero.Defs

@[expose] public section

/-! The diagonal-translation bridge to the reviewed, denominator-cleared
literal order. The unshifted matrix is compared with a shifted exact target,
not with the ordinary exact target. -/
namespace RKResearch.DiagonalTreeShift

open RKResearch
open scoped Matrix

noncomputable section

/-- The normalized coefficient of a literal rooted tree. -/
def exactFlowOutput (K : Type*) [Field K] (t : FiniteRootedTree) : K :=
  (t.factorial : K)⁻¹

variable {ι K : Type*} [Fintype ι] [Field K]

private theorem factorial_cast_ne_zero [CharZero K] (t : FiniteRootedTree) :
    (t.factorial : K) ≠ 0 := by
  change (((t.factorial : ℕ) : K)) ≠ 0
  exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt t.factorial.pos)

private theorem hasOrder_iff_exactFlow [CharZero K] (p : ℕ) (A : Matrix ι ι K) (b : ι → K) :
    RKResearch.HasOrder p A b ↔ AgreesThrough p (fun t => b ⬝ᵥ Φ t A) (exactFlowOutput K) := by
  constructor
  · intro h t ht
    change b ⬝ᵥ Φ t A = exactFlowOutput K t
    have hn := factorial_cast_ne_zero (K := K) t
    exact mul_left_cancel₀ hn ((h t ht).trans (mul_inv_cancel₀ hn).symm)
  · intro h t ht
    change (t.factorial : K) * (b ⬝ᵥ Φ t A) = 1
    rw [show b ⬝ᵥ Φ t A = exactFlowOutput K t from h t ht]
    exact mul_inv_cancel₀ (factorial_cast_ne_zero (K := K) t)

variable [DecidableEq ι]

private theorem output_shift (B : Matrix ι ι K) (b : ι → K) (γ : K) :
    transform K γ (fun t => b ⬝ᵥ Φ t B) =
      fun t => b ⬝ᵥ Φ t (B + γ • (1 : Matrix ι ι K)) := by
  funext t
  exact transform_tableau_output B b γ t

/-- To test the shifted matrix for literal order, compare the unshifted
output with the exact-flow target shifted by the opposite coefficient. -/
theorem hasOrder_add_diagonal_iff [CharZero K] (p : ℕ) (B : Matrix ι ι K) (b : ι → K) (γ : K) :
    RKResearch.HasOrder p (B + γ • (1 : Matrix ι ι K)) b ↔
      AgreesThrough p (fun t => b ⬝ᵥ Φ t B) (transform K (-γ) (exactFlowOutput K)) := by
  rw [hasOrder_iff_exactFlow p (B + γ • (1 : Matrix ι ι K)) b]
  simpa only [output_shift B b γ, transform_neg_right] using
    agreesThrough_transform_iff K γ p (fun t => b ⬝ᵥ Φ t B) (transform K (-γ) (exactFlowOutput K))

/-- The least differing literal order is unchanged by the same translation. -/
theorem firstDifference_add_diagonal_iff (n : ℕ) (B : Matrix ι ι K) (b : ι → K) (γ : K) :
    FirstDifferenceAt n (fun t => b ⬝ᵥ Φ t (B + γ • (1 : Matrix ι ι K))) (exactFlowOutput K) ↔
      FirstDifferenceAt n (fun t => b ⬝ᵥ Φ t B) (transform K (-γ) (exactFlowOutput K)) := by
  simpa only [output_shift B b γ, transform_neg_right] using
    firstDifference_transform_iff K γ n (fun t => b ⬝ᵥ Φ t B) (transform K (-γ) (exactFlowOutput K))

end
end RKResearch.DiagonalTreeShift
