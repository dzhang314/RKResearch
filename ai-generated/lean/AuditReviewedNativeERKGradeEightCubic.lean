import RKCert.ReviewedNative.ERKGradeEightCubic

open RKResearch RKResearch.Certified.Graded Polynomial Module RKCert.Endpoint

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26 → K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b 17) {r : ℕ}
    {U : Submodule K (Fin 26 → K)} {w : Fin 26 → K}
    (H : FlatClockHead A 5 3 r U w) : zeroSpace A 3 ≤ U :=
  grade_eight_third_inside_core ha ho (by decide) H

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K[X]) (degree : P.natDegree≤3) (nonzero : P≠0) :
    0 < (formalPrimitive (X*P^2)).eval (-1:K) :=
  primitive_x_cubic_square_pos P degree nonzero (neg_ne_zero.mpr one_ne_zero)

#print axioms RKCert.Endpoint.primitive_x_cubic_square_pos
#print axioms RKResearch.Certified.Graded.grade_eight_cubic_chronology
#print axioms RKResearch.Certified.Graded.grade_eight_third_inside_core
#print axioms RKResearch.Certified.Graded.grade_eight_remaining_two_cases
