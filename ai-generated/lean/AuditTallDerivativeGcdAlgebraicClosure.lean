module

public import RKCert.ReviewedNative.TallDerivativeGcdAlgebraicClosure

@[expose] public section

open RKResearch Polynomial RKResearch.Certified.TallFiniteResponse
open scoped Matrix Polynomial

variable {K : Type*} [Field K] [CharZero K]
variable {s p : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {P Q : K[X]}

example (hQ : Q ≠ 0) :
    derivativeGcdQuotientDegree Q = (Q.rootSet (AlgebraicClosure K)).ncard :=
  derivativeGcdQuotientDegree_eq_ncard_rootSet_algebraicClosure Q hQ

example (hf : Fraction A b P Q) (ho : HasOrder p A b) :
    p ≤ P.natDegree + (Q.rootSet (AlgebraicClosure K)).ncard :=
  hf.order_le_num_add_algebraicClosureRootSet ho

#print axioms derivativeGcdQuotientDegree_eq_ncard_rootSet_algebraicClosure
#print axioms Fraction.order_le_num_add_algebraicClosureRootSet
