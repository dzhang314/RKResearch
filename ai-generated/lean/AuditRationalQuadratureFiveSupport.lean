module

import RKCert.ReviewedNative.RationalQuadratureFiveSupport

open RKResearch
open RKResearch.Certified.RationalQuadratureFive
open scoped BigOperators Matrix

example (r : ℚ) : ¬ IsSquare (12 * (25 * r^4 - 22 * r^2 + 5)) :=
  centered_discriminant_not_isSquare r

example (r u v : ℚ) (h0 : threeNodeUnitMean r u v = 0)
    (h1 : threeNodeUnitXMean r u v = 0) : False :=
  no_rational_unit_three_roots r u v h0 h1

example {ι X K : Type*} [Fintype ι] [Semiring K]
    (b : ι → K) (c : ι → X) (f : X → K) :
    (∑ i, b i * f (c i)) =
      ∑ x ∈ activeQuadratureSites b c, quadratureSiteWeight b c x * f x :=
  weighted_sum_eq_activeQuadratureSites b c f

example {K : Type*} [Field K] [CharZero K] (T : Finset K) (μ : K → K)
    (hrat : ∀ x ∈ T, ∃ q : ℚ, x = (q : K))
    (law : ∀ k : ℕ, k ≤ 4 → (∑ x ∈ T, μ x * x^k) = 1 / ((k+1 : ℕ) : K)) :
    4 ≤ T.card :=
  four_le_of_rational_grouped_unit_moments_five T μ hrat law

example {ι K : Type*} [Fintype ι] [Field K] [CharZero K]
    {p : ℕ} {b c : ι → K} (h : HasQuadratureOrder p b c) (hp : 5 ≤ p)
    (hrat : ∀ x ∈ activeQuadratureSites b c, ∃ q : ℚ, x = (q : K)) :
    4 ≤ (activeQuadratureSites b c).card :=
  h.four_le_activeQuadratureSites_of_rat hp hrat

example {ι K : Type*} [Fintype ι] [Field K] [CharZero K]
    {p : ℕ} {A : Matrix ι ι K} {b : ι → K} (h : HasOrder p A b) (hp : 5 ≤ p)
    (hrat : ∀ x ∈ activeQuadratureSites b (A *ᵥ 1), ∃ q : ℚ, x = (q : K)) :
    4 ≤ (activeQuadratureSites b (A *ᵥ 1)).card :=
  h.four_le_activeQuadratureSites_of_rat hp hrat

example {ι : Type*} [Fintype ι] {A : Matrix ι ι ℚ} {b : ι → ℚ}
    (h : HasOrder 5 A b) : 4 ≤ (activeQuadratureSites b (A *ᵥ 1)).card :=
  h.four_le_activeQuadratureSites_rat le_rfl

#print axioms RKResearch.Certified.RationalQuadratureFive.centered_discriminant_not_isSquare
#print axioms RKResearch.weighted_sum_eq_activeQuadratureSites
#print axioms RKResearch.four_le_of_rational_grouped_unit_moments_five
#print axioms RKResearch.HasOrder.four_le_activeQuadratureSites_of_rat
