module

import RKCert.ReviewedNative.RationalCommonDiagonalStageFloor

open Polynomial
open RKResearch RKResearch.Certified
open scoped BigOperators Matrix Polynomial

example {R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Field K] [Algebra R K] [IsFractionRing R K] {P : R[X]} {x : K} {q : R}
    (hq : Prime q) (hP : P.Monic) (hh : ∀ j < P.natDegree, q ∣ P.coeff j)
    (hx : aeval x P = 0) :
    ∃ z : R, x = algebraMap R K z ∧ q ∣ z :=
  exists_integer_dvd_of_monic_aeval_eq_zero hq hP hh hx

example {q j : ℕ} [Fact q.Prime] (hq : 2 < q) (hj : 0 < j) :
    multiplicity q ((j + 1).factorial) < j :=
  factorial_succ_multiplicity_lt_of_two_lt hq hj

example {q : ℕ} [Fact q.Prime] (hq : 2 < q)
    (S : Finset ℕ) (hS : ∀ j ∈ S, 0 < j) (a : ℕ → ℤ) {x : ℤ}
    (hx : (q : ℤ) ∣ x) :
    (1 + ∑ j ∈ S, (a j : ℚ) * (x : ℚ) ^ j / ((j + 1).factorial : ℚ)) ≠ 0 :=
  one_add_factorial_power_sum_ne_zero_of_dvd hq S hS a hx

example {m : ℕ} (hm : 2 ≤ m) (x : ℚ) :
    aeval x (commonDiagonalTallPolynomial m) ≠ 0 :=
  commonDiagonalTallPolynomial_no_rat_root hm x

example {K : Type*} [Field K] [CharZero K] {m : ℕ} (hm : 2 ≤ m) (x : ℚ) :
    (∑ k ∈ Finset.range (m + 1),
      (m.choose k : K) * (-(x : K)) ^ (m - k) / ((k + 1).factorial : K)) ≠ 0 :=
  commonDiagonalTallBinomial_ratCast_ne_zero hm x

example {K : Type*} [Field K] [CharZero K] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {x : ℚ}
    (ho : HasOrder p A b) (ha : A.IsLowerTriangular)
    (hc : ∀ i, A i i = (x : K)) (hp : 3 ≤ p) : p ≤ s :=
  ho.common_diagonal_stage_floor_of_ratCast ha hc hp

example {s p : ℕ} {A : Matrix (Fin s) (Fin s) ℚ} {b : Fin s → ℚ} {x : ℚ}
    (ho : HasOrder p A b) (ha : A.IsLowerTriangular)
    (hc : ∀ i, A i i = x) (hp : 3 ≤ p) : p ≤ s :=
  ho.rat_common_diagonal_stage_floor ha hc hp

#print axioms RKResearch.Certified.exists_integer_dvd_of_monic_aeval_eq_zero
#print axioms RKResearch.Certified.one_add_factorial_power_sum_ne_zero_of_dvd
#print axioms RKResearch.Certified.commonDiagonalTallPolynomial_no_rat_root
#print axioms RKResearch.HasOrder.common_diagonal_stage_floor_of_ratCast
