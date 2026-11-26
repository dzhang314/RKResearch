module

import RKCert.ReviewedNative.ShiftedTallReference

open RKResearch RKResearch.FiniteRootedTree RKResearch.DiagonalTreeShift
open scoped FiniteRootedTree Matrix BigOperators

section

variable {K : Type*} [Field K]

example (a : K) (n : ℕ) (f : FiniteRootedTree → K) :
    transform K a f (tallTree n.succPNat) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : K) * a ^ (n - k) *
        f (tallTree k.succPNat) :=
  transform_tallTree_eq_binomial a n f

variable [CharZero K]

example (a : K) (n : ℕ) :
    ((n : K) + 3) * transform K a (exactFlowOutput K) (tallTree (n + 2).succPNat) =
      (1 + 2 * ((n : K) + 2) * a) *
        transform K a (exactFlowOutput K) (tallTree (n + 1).succPNat) -
      ((n : K) + 1) * a ^ 2 * transform K a (exactFlowOutput K) (tallTree n.succPNat) :=
  shiftedExactTall_recurrence a n

example (γ : K) (n : ℕ) :
    shiftedExactTall (-γ) n = 0 → shiftedExactTall (-γ) (n + 1) ≠ 0 :=
  shiftedExactTall_succ_ne_zero_of_eq_zero (-γ) n

example {ι : Type*} [Fintype ι] [DecidableEq ι] {p n : ℕ}
    (B : Matrix ι ι K) (b : ι → K) (γ : K)
    (ho : RKResearch.HasOrder p (B + γ • (1 : Matrix ι ι K)) b) (pay : n + 2 ≤ p) :
    (b ⬝ᵥ Φ (tallTree n.succPNat) B ≠ 0) ∨
      (b ⬝ᵥ Φ (tallTree (n + 1).succPNat) B ≠ 0) :=
  paid_shifted_tall_nonzero_pair (n := n) B b γ ho pay

end

#check @RKResearch.DiagonalTreeShift.transform_tallTree_eq_binomial
#check @RKResearch.DiagonalTreeShift.shiftedExactTall_eq_sum
#check @RKResearch.DiagonalTreeShift.shiftedExactTall_recurrence
#check @RKResearch.DiagonalTreeShift.shiftedExactTall_succ_ne_zero_of_eq_zero
#check @RKResearch.DiagonalTreeShift.shiftedExactTall_nonzero_pair
#check @RKResearch.DiagonalTreeShift.paid_shifted_tall_nonzero_pair

#print axioms RKResearch.DiagonalTreeShift.transform_tallTree_eq_binomial
#print axioms RKResearch.DiagonalTreeShift.shiftedExactTall_recurrence
#print axioms RKResearch.DiagonalTreeShift.shiftedExactTall_succ_ne_zero_of_eq_zero
#print axioms RKResearch.DiagonalTreeShift.shiftedExactTall_nonzero_pair
#print axioms RKResearch.DiagonalTreeShift.paid_shifted_tall_nonzero_pair
