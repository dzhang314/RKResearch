module

public import RKCert.ReviewedNative.CommonDiagonalTallObstruction
public import RKCert.ReviewedNative.RationalCommonDiagonalTallScalar
public import Mathlib.Data.Rat.Cast.CharZero

@[expose] public section

/-! # An all-order stage floor for rational common diagonals

Only the shared diagonal is required to be rational. The other entries
and weights can lie in any characteristic-zero field. No strictness,
weight positivity, minimality, or additional tableau order convention
is used. -/

namespace RKResearch.Certified

open scoped BigOperators

theorem commonDiagonalTallBinomial_ratCast_ne_zero
    {K : Type*} [Field K] [CharZero K] {m : ℕ} (hm : 2 ≤ m) (x : ℚ) :
    commonDiagonalTallBinomial m (x : K) ≠ 0 := by
  have h := (Rat.castHom K).injective.ne (commonDiagonalTallBinomial_ne_zero hm x)
  simpa only [commonDiagonalTallBinomial, map_sum, map_div₀, map_mul, map_pow,
    map_natCast, map_neg, map_zero, Rat.coe_castHom] using h

end RKResearch.Certified

namespace RKResearch

open scoped Matrix

/-- A common-diagonal tableau whose clock is rational needs at least
`p` stages at every paid order `p ≥ 3`. The bound also rules out smaller
and empty tableaux without assuming a minimum stage count in advance. -/
theorem HasOrder.common_diagonal_stage_floor_of_ratCast
    {K : Type*} [Field K] [CharZero K] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {x : ℚ}
    (ho : HasOrder p A b) (ha : A.IsLowerTriangular)
    (hc : ∀ i, A i i = (x : K)) (hp : 3 ≤ p) : p ≤ s := by
  by_contra h
  have hm : 2 ≤ p - 1 := by omega
  have htail : Certified.commonDiagonalTallBinomial (p - 1) (x : K) = 0 :=
    ho.common_diagonal_tall_binomial_obstruction ha hc (p - 1) (by omega) (by omega)
  exact Certified.commonDiagonalTallBinomial_ratCast_ne_zero hm x htail

/-- Rational-tableau specialization, including a zero common diagonal. -/
theorem HasOrder.rat_common_diagonal_stage_floor
    {s p : ℕ} {A : Matrix (Fin s) (Fin s) ℚ} {b : Fin s → ℚ} {x : ℚ}
    (ho : HasOrder p A b) (ha : A.IsLowerTriangular)
    (hc : ∀ i, A i i = x) (hp : 3 ≤ p) : p ≤ s :=
  ho.common_diagonal_stage_floor_of_ratCast (x := x) ha hc hp

/-- In the rational-diagonal chart, stage counts starting at two
also give an order ceiling, even when the paid order is small. -/
theorem HasOrder.common_diagonal_order_le_stages_of_ratCast
    {K : Type*} [Field K] [CharZero K] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {x : ℚ}
    (ho : HasOrder p A b) (ha : A.IsLowerTriangular)
    (hc : ∀ i, A i i = (x : K)) (hs : 2 ≤ s) : p ≤ s := by
  by_cases hp : 3 ≤ p
  · exact ho.common_diagonal_stage_floor_of_ratCast ha hc hp
  · omega

end RKResearch
