import RKCert.ReviewedNative.DIRK12MidpointPrimeCRT

open RKResearch
open RKResearch.Certified.DualSupport12VectorReplay (nextTree)
open RKResearch.Certified.DIRK12MidpointPrimeCRT
open scoped Matrix FiniteRootedTree

set_option autoImplicit false

example : HasOrder 12 A b := paid

example : IsUnit (((nextTree.factorial : Nat) : K) * (b ⬝ᵥ Φ nextTree A)-1) :=
  unit_next

example (S : Type) [CommRing S] [Nontrivial S] (h : ((M : Nat) : S) = 0) :
    ∃ (U : Matrix (Fin 15) (Fin 15) S) (w : Fin 15 → S),
      U.IsLowerTriangular ∧ U 0 0 ≠ U 1 1 ∧ HasOrder 12 U w ∧ ¬ HasOrder 13 U w :=
  exact_of_modulus_zero S h

example (S : Type) [CommRing S] [Nontrivial S] (e : Nat) [CharP S (131^e)] (he : e ≤ 20) :
    ∃ (U : Matrix (Fin 15) (Fin 15) S) (w : Fin 15 → S),
      U.IsLowerTriangular ∧ U 0 0 ≠ U 1 1 ∧ HasOrder 12 U w ∧ ¬ HasOrder 13 U w :=
  exact_of_dvd S _ (divisor_131 e he)

example (S : Type) [CommRing S] [Nontrivial S] (e : Nat) [CharP S (149^e)] (he : e ≤ 20) :
    ∃ (U : Matrix (Fin 15) (Fin 15) S) (w : Fin 15 → S),
      U.IsLowerTriangular ∧ U 0 0 ≠ U 1 1 ∧ HasOrder 12 U w ∧ ¬ HasOrder 13 U w :=
  exact_of_dvd S _ (divisor_149 e he)

#print axioms RKResearch.Certified.DIRK12MidpointPrimeCRT.paid_of_dvd
#print axioms RKResearch.Certified.DIRK12MidpointPrimeCRT.exact_of_modulus_zero
#print axioms RKResearch.Certified.DIRK12MidpointPrimeCRT.exact_131
#print axioms RKResearch.Certified.DIRK12MidpointPrimeCRT.exact_149
