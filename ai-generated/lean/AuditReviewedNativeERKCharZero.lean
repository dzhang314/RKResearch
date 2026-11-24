module
import RKCert.ReviewedNative.ERKCharZero
import Mathlib.Data.ZMod.Basic

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse Module
universe u

section Field
variable {K : Type u} [Field K] {s p q : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
variable (ha : ∀ i j, i ≤ j → A i j=0)

/-- A future rank from the doubling band can be plugged into the numerical
join with no characteristic premise on the join itself. -/
example (h : HasOrder 20 A b) (r : 11≤finrank K (zeroSpace A 10)) : 30≤s :=
  erk_count_of_midpoint_rank ha h (by decide) 1 r

variable [CharZero K]
example (h : HasOrder p A b) (hq : 5≤q) (pay : 2*q≤p) : q≤finrank K (zeroSpace A q) :=
  erk_grade_five_rank_at_paid_midpoint ha h hq pay
end Field

section Ring
variable {R : Type u} [CommRing R] [CharZero R] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R} (ha : ∀ i j, i ≤ j → A i j=0)

example (h : HasOrder p A b) (hp : 10≤p) : (3*p+1)/2-1≤s :=
  h.erk_grade_five_charZero_stages ha hp

example (h : HasOrder 10 A b) : 14≤s := h.erk_grade_five_charZero_stages ha (by decide)
example (h : HasOrder 11 A b) : 16≤s := h.erk_grade_five_charZero_stages ha (by decide)
example (h : HasOrder 12 A b) : 17≤s := h.erk_grade_five_charZero_stages ha (by decide)
example (h : HasOrder 13 A b) : 19≤s := h.erk_grade_five_charZero_stages ha (by decide)
end Ring

/-- The first projection retains characteristic zero; the other factor
gives both zero divisors and actual additive torsion. -/
example {s : ℕ} {A : Matrix (Fin s) (Fin s) (ℚ × ZMod 2)} {b : Fin s → (ℚ × ZMod 2)}
    (h : HasOrder 10 A b) (ha : ∀ i j, i ≤ j → A i j=0) : 14≤s := by
  let _ : CharZero (ℚ × ZMod 2) :=
    ⟨fun _ _ e => Nat.cast_injective (R:=ℚ) (congrArg Prod.fst e)⟩
  exact h.erk_grade_five_charZero_stages ha (by decide)

#check RKResearch.HasOrder.erk_grade_five_charZero_stages
#check erk_count_of_midpoint_rank
#print axioms erk_count_of_midpoint_rank
#print axioms erk_rank_interval_of_coeff_sep
#print axioms erk_paid_rank_interval
#print axioms erk_grade_five_rank_at_paid_midpoint
#print axioms RKResearch.HasOrder.strict_lower_triangular_of_charZero_fields
#print axioms RKResearch.HasOrder.erk_grade_five_charZero_stages_field
#print axioms RKResearch.HasOrder.erk_grade_five_charZero_stages
