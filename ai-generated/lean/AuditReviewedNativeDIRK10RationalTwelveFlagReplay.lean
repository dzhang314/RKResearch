import RKCert.ReviewedNative.DIRK10RationalTwelveFlagRings

open RKResearch RKResearch.Certified
open scoped Matrix

example :
    ∃ (A : Matrix (Fin 12) (Fin 12) ℚ) (b : Fin 12 → ℚ),
      A.IsLowerTriangular ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b :=
  DIRK10RationalTwelveFlagReplay.exists_exact

example {R : Type*} [CommRing R] [Nontrivial R]
    (h : IsUnit (DIRK10RationalTwelveFlagReplay.denominator : R)) :
    ∃ (A : Matrix (Fin 12) (Fin 12) R) (b : Fin 12 → R),
      A.IsLowerTriangular ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b :=
  DIRK10RationalTwelveFlagReplay.exists_exact_of_unit h

#print axioms DIRK10RationalTwelveFlagReplay.order_ten
#print axioms DIRK10RationalTwelveFlagReplay.not_order_eleven
#print axioms DIRK10RationalTwelveFlagReplay.exists_exact
#print axioms DIRK10RationalTwelveFlagReplay.exists_exact_of_unit
