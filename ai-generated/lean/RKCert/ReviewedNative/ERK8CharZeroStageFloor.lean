module

public import RKCert.ReviewedNative.ERK8FourOffCharZero
public import RKCert.ERK8OneOffFin10
public import RKCert.ReviewedNative.StagePadding
public import RKCert.ReviewedNative.CoefficientField
public import RKResearch.ERK

import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Exact characteristic-zero stage floor for ERK order eight
Both branches of the paid width-ten census are closed on literal
tableaux. Zero padding and specialization then transport the result
to arbitrary characteristic-zero commutative rings. -/
namespace RKResearch.Certified.ERK8CharZero

open RKResearch Graded Graded.OneOff Graded.ERK8PaidField Graded.FourOffNewton
open StagePadding
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K]

theorem no_order8_fin10
    (A : Matrix (Fin 10) (Fin 10) K) (b : Fin 10→K)
    (ha : ERK A) (ho : HasOrder 8 A b) : False := by
  obtain ⟨mid,census⟩ := order8_paid_one_or_four_with_horizon ha ho (by norm_num : (11:K)≠0)
  rcases census with one|four
  · exact Graded.OneOff.Eight.erk8_one_off_exclusion ha ho mid one
  · exact no_four_off_charZero ha ho four

theorem stages_at_least_eleven_field {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ha : ERK A) (ho : HasOrder 8 A b) : 11≤s :=
  Nat.succ_le_of_lt (strict_stages_gt_of_exact_exclusion no_order8_fin10 ha ho)

universe u

variable {R : Type u} [CommRing R] [CharZero R]

/-- No integral-domain or ordered-field hypothesis is required on the
coefficient ring. The auxiliary characteristic-zero field is chosen
to avoid all nonzero natural scalar multiples of one. -/
theorem stages_at_least_eleven {s : ℕ} {A : Matrix (Fin s) (Fin s) R} {b : Fin s→R}
    (ha : ERK A) (ho : HasOrder 8 A b) : 11≤s := by
  refine RKCert.ReviewedNative.with_charZero_field (R:=R) ?_
  intro F _ _ f
  have strict : ERK (A.map f) := by
    intro i j ij
    change f (A i j)=0
    rw [ha ij,map_zero]
  exact stages_at_least_eleven_field strict (HasOrder.map ho f)

end RKResearch.Certified.ERK8CharZero

#print axioms RKResearch.Certified.ERK8CharZero.no_order8_fin10
#print axioms RKResearch.Certified.ERK8CharZero.stages_at_least_eleven_field
#print axioms RKResearch.Certified.ERK8CharZero.stages_at_least_eleven
