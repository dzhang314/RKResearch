module

public import RKCert.ReviewedNative.TallDerivativeGcdRootSet
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

/-! # The geometric pole count over the actual algebraic closure -/

namespace RKResearch.Certified.TallFiniteResponse

open RKResearch Polynomial
open scoped Matrix Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The degree difference counts distinct roots in the algebraic
closure. No splitting hypothesis on `K` is made. -/
theorem derivativeGcdQuotientDegree_eq_ncard_rootSet_algebraicClosure
    (Q : K[X]) (hQ : Q ≠ 0) :
    derivativeGcdQuotientDegree Q = (Q.rootSet (AlgebraicClosure K)).ncard :=
  derivativeGcdQuotientDegree_eq_ncard_rootSet_of_splits (L := AlgebraicClosure K)
    Q hQ (IsAlgClosed.splits (Q.map (algebraMap K (AlgebraicClosure K))))

variable {s p : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {P Q : K[X]}

/-- Tall order over characteristic zero pays at most the numerator
degree plus the number of distinct geometric poles. For a nonreduced
pair the root set counts the submitted denominator, not just its
retained poles. -/
theorem Fraction.order_le_num_add_algebraicClosureRootSet
    (hf : Fraction A b P Q) (ho : HasOrder p A b) :
    p ≤ P.natDegree + (Q.rootSet (AlgebraicClosure K)).ncard := by
  have hQ : Q ≠ 0 := by
    intro hz
    have hc := hf.den_zero
    rw [hz, Polynomial.coeff_zero] at hc
    exact zero_ne_one hc
  simpa only [derivativeGcdQuotientDegree_eq_ncard_rootSet_algebraicClosure Q hQ] using
    (hf.order_le_num_add_derivativeGcd ho)

end
end RKResearch.Certified.TallFiniteResponse
