import RKCert.ReviewedNative.DIRK12FactorialTwentyFlag

open RKResearch
open RKResearch.Certified.DIRK12FactorialTwentyFlag
open scoped Matrix

example {R : Type*} [CommRing R] [Nontrivial R] (h : IsUnit (Nat.factorial 12:R)) :
    ∃ (U : Matrix (Fin 20) (Fin 20) R) (w : Fin 20→R),
      U.IsLowerTriangular ∧ U 0 0=0 ∧ (16:R)*U 1 1=1 ∧
      HasOrder 12 U w ∧ ¬ HasOrder 13 U w :=
  exists_exact_factorial h

#check @exists_exact_factorial
#print axioms RKResearch.Certified.DIRK12FactorialTwentyFlag.exists_exact_factorial
#print axioms RKResearch.Certified.ScaledIntegerFlagReplay.transport
