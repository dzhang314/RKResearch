module

import RKCert.ReviewedNative.BetaGapScalar

open RKResearch.Certified.Graded.BetaGapScalar
open scoped BigOperators

section

variable {K : Type*} [Field K]

/-- The eliminated-coefficient test includes d = 1 without a synthetic row. -/
example (r : ℕ)
    (paid : ∀ n : ℕ, 0 < n → n ≤ 1 + 2 * r + 1 → (n : K) ≠ 0)
    (a : Fin (r + 2) → K) (endpoint : (∑ j : Fin (r + 2), a j) = 0)
    (test : ∀ i : Fin (r + 1),
      (∑ j : Fin (r + 2), a j / ((1 + i.val + j.val : ℕ) : K)) = 0) :
    a = 0 :=
  betaCoefficients_zero (d := 1) Nat.zero_lt_one paid a endpoint test

/-- The physical label map need not be injective. -/
example {ι : Type*} [Fintype ι] (x w : ι → K) (κ : K) {d r : ℕ} (positive : 0 < d)
    (paid : ∀ n : ℕ, 0 < n → n ≤ d + 2 * r + 1 → (n : K) ≠ 0)
    (moment : ∀ q : ℕ, q ≤ 2 * r →
      κ * ((d + q : ℕ) : K) * ((d + q + 1 : ℕ) : K) *
        (∑ s : ι, w s * x s ^ q) = 1) :
    r + 1 ≤ Fintype.card ι :=
  card_succ_le_of_cleared_beta_moments x w κ positive paid moment

end

#check @RKResearch.Certified.Graded.BetaGapScalar.betaCoefficients_zero
#check @RKResearch.Certified.Graded.BetaGapScalar.card_succ_le_of_cleared_beta_moments

#print axioms RKResearch.Certified.Graded.BetaGapScalar.betaCoefficients_zero
#print axioms RKResearch.Certified.Graded.BetaGapScalar.card_succ_le_of_cleared_beta_moments
