module

import RKCert.ReviewedNative.RationalSmallSDIRKLower

open Polynomial IsFractionRing
open scoped Polynomial Matrix BigOperators

namespace RKResearch.Certified

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

example (P : ℤ[X]) (x : ℚ) (hx : aeval x P = 0)
    (h : (Int.castRingHom (ZMod 5)) P.leadingCoeff ≠ 0) :
    (Int.castRingHom (ZMod 5)) (den ℤ x : ℤ) ≠ 0 ∧
      (P.map (Int.castRingHom (ZMod 5))).IsRoot
        ((Int.castRingHom (ZMod 5)) (num ℤ x) /
          (Int.castRingHom (ZMod 5)) (den ℤ x : ℤ)) :=
  ⟨fractionRoot_den_map_ne_zero _ hx h, fractionRoot_reduces_of_leadingCoeff_ne_zero _ hx h⟩

variable {s p : ℕ} {A : Matrix (Fin s) (Fin s) ℚ} {b : Fin s → ℚ} {γ : ℚ}

example (ho : HasOrder p A b) (ha : A.IsLowerTriangular)
    (hc : ∀ i, A i i = γ) (pay : 3 ≤ p) : 3 ≤ s :=
  ho.rat_common_diagonal_order_three_stages ha hc pay

example (ho : HasOrder p A b) (ha : A.IsLowerTriangular)
    (hc : ∀ i, A i i = γ) (pay : 4 ≤ p) : 4 ≤ s :=
  ho.rat_common_diagonal_order_four_stages ha hc pay

example (h : 3 ∈ rationalStrictSDIRKStages 3) :
    IsLeast (rationalStrictSDIRKStages 3) 3 ∧ IsLeast (rationalStrictSDIRKExactStages 3) 3 :=
  rational_strictSDIRK_three_minima_of_witness h

example (h : 4 ∈ rationalStrictSDIRKStages 4) :
    IsLeast (rationalStrictSDIRKStages 4) 4 ∧ IsLeast (rationalStrictSDIRKExactStages 4) 4 :=
  rational_strictSDIRK_four_minima_of_witness h

#print axioms fractionRoot_reduces_of_leadingCoeff_ne_zero
#print axioms RKResearch.HasOrder.common_diagonal_tall_binomial_obstruction
#print axioms RKResearch.HasOrder.rat_common_diagonal_order_three_stages
#print axioms RKResearch.HasOrder.rat_common_diagonal_order_four_stages
#print axioms rational_strictSDIRK_three_minima_of_witness
#print axioms rational_strictSDIRK_four_minima_of_witness

end RKResearch.Certified
