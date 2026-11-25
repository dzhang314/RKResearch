module

import RKCert.ReviewedNative.TallPoleMultiplierProducer

open RKResearch RKResearch.Certified.TallFiniteResponse Polynomial
open scoped Matrix Polynomial

variable {K : Type*} [Field K] {s p : ℕ} {Q P : K[X]}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

example (hQ : Q ≠ 0) :
    ∃ V B : K[X], PoleMultiplier Q (derivativeGcdQuotientDegree Q) V B :=
  exists_pole_multiplier_of_gcd Q hQ

example [CharZero K] (hf : Fraction A b P Q) (ho : HasOrder p A b) :
    p ≤ P.natDegree+derivativeGcdQuotientDegree Q :=
  hf.order_le_num_add_derivativeGcd ho

#print axioms PoleMultiplier.of_derivative_factors
#print axioms exists_pole_multiplier_of_gcd
#print axioms Fraction.order_le_num_add_derivativeGcd
