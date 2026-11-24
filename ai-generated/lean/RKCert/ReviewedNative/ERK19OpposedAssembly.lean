module

public import RKCert.ReviewedNative.StagePadding
public import RKCert.ReviewedNative.ERK19LocalNonzeroClose
public import RKCert.ReviewedNative.ERK19ZeroOpposedAdapter

@[expose] public section

/-! The ordered order-19 stage bound reduces to the opposed-window
scalar theorem. Both tableau reductions are independent of that theorem. -/

namespace RKResearch.Certified.ERK19

open RKResearch RKResearch.Certified.Graded.Reverse
open Polynomial RKCert.ReviewedNative.ERK19ZeroScalar

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem ordered_erk19_stage_floor30_of_zero_scalar
    (scalar : ∀ (P : K[X]) (z : Fin 4 → K) (e : ℕ),
      OpposedQuinticWindows P z e → False)
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 19 A b) : 30 ≤ s := by
  have impossible (T : Matrix (Fin 29) (Fin 29) K) (w : Fin 29 → K)
      (ht : ∀ i j, i ≤ j → T i j = 0) (hw : HasOrder 19 T w) : False := by
    classical
    by_cases h : firstSeed T w = 0
    · exact width29_zero_first_seed_impossible_of_scalar scalar ht hw h
    · exact width29_nonzero_first_seed_impossible ht hw h
  have gt : 29 < s := RKResearch.Certified.StagePadding.strict_stages_gt_of_exact_exclusion
    (n := 29) (p := 19) impossible ha ho
  exact Nat.succ_le_of_lt gt

end RKResearch.Certified.ERK19
