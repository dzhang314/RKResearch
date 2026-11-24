module

public import RKCert.ReviewedNative.ERKOrder16PaidFrame

@[expose] public section

/-! # The native width-24 seed and seventh-rank split

The exact even midpoint uses the explicit origin for separation.
This file contains no scalar gate, trace census, or head computation. -/
namespace RKResearch.Certified.ERK16

open RKResearch Module
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}

section RankSplit
variable [CharZero K]

/-- Once the actual eighth defect rank equals nine, the seventh-rank
split is purely characteristic-zero; this lemma does not earn F8=9. -/
theorem width24_seventh_rank_cases_of_eighth
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b)
    (f8 : finrank K (zeroSpace A 8) = 9) :
    finrank K (zeroSpace A 7) = 7 ∨ finrank K (zeroSpace A 7) = 8 := by
  have sep := explicit_coeff_separated (s := 23) ha ho (q := 8) (by decide)
  have f5 := grade_five_surplus_of_reviewed_order ha ho (by decide : 10 ≤ 16)
  have step5 := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separation ha sep (j := 5) (by decide) (by decide))
  have step6 := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separation ha sep (j := 6) (by decide) (by decide))
  have step7 := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separation ha sep (j := 7) (by decide) (by decide))
  change finrank K (zeroSpace A 5) < finrank K (zeroSpace A 6) at step5
  change finrank K (zeroSpace A 6) < finrank K (zeroSpace A 7) at step6
  change finrank K (zeroSpace A 7) < finrank K (zeroSpace A 8) at step7
  omega

end RankSplit

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Independently of constructing the terminal frame, the checked
nonzero-first-seed stage floor rules out that branch at width 24. -/
theorem width24_first_seed_eq_zero
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b) :
    firstSeed A b = 0 := by
  by_contra nonzero
  have floor : 25 ≤ (24 : ℕ) := ordered_stage_floor25_of_nonzero_first ha ho nonzero
  exact (by decide : ¬ (25 : ℕ) ≤ 24) floor

/-- The native ordered frame has already earned the eighth rank on
these same original physical rows. -/
theorem width24_seventh_rank_cases_of_frame
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b)
    (F : Width24PaidFrame A b) :
    finrank K (zeroSpace A 7) = 7 ∨ finrank K (zeroSpace A 7) = 8 :=
  width24_seventh_rank_cases_of_eighth ha ho F.forward

/-- Raw all-tree input: no prescribed seed, last row, or defect rank. -/
theorem width24_seed_zero_and_seventh_rank_cases
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b) :
    firstSeed A b = 0 ∧
      (finrank K (zeroSpace A 7) = 7 ∨ finrank K (zeroSpace A 7) = 8) :=
  ⟨width24_first_seed_eq_zero ha ho,
    width24_seventh_rank_cases_of_frame ha ho (width24_paid_frame ha ho)⟩

end RKResearch.Certified.ERK16
