module
import RKCert.ReviewedNative.DIRKGradeSixInvariantJoin

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse Module
universe u

section Field
variable {K : Type u} [Field K] {s p : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
variable (ha : A.IsLowerTriangular)

example (h : HasOrder 12 A b)
    (g : finrank K (zeroSpace A 3)+4 ≤ finrank K (zeroSpace A 6)) : 15 ≤ s :=
  dirk_order_twelve_of_grade_six ha h g
example (h : HasOrder 13 A b)
    (g : finrank K (zeroSpace A 3)+4 ≤ finrank K (zeroSpace A 6)) : 17 ≤ s :=
  dirk_order_thirteen_of_grade_six ha h g
example (h : HasOrder 14 A b) (nc : monomialStageDefect A 1 ≠ 0)
    (g : finrank K (zeroSpace A 3)+4 ≤ finrank K (zeroSpace A 6)) : 19 ≤ s :=
  dirk_even_nonC2_of_grade_six ha h (m:=7) (by decide) (by decide) nc g
example (h : HasOrder 15 A b)
    (g : finrank K (zeroSpace A 3)+4 ≤ finrank K (zeroSpace A 6)) : 20 ≤ s :=
  dirk_order_fifteen_of_grade_six ha h g

/-- The new reverse inequality does not take the as-yet incomplete grade-six surplus. -/
example (h : HasOrder 15 A b) : finrank K (treeSpace A 6)+7 ≤ s :=
  dirk_reverse_room_unanchored ha h (q:=6) (n:=7) (by decide) (by decide) (by decide)

variable [CharZero K]
example (h : HasOrder 12 A b) (inv : (zeroSpace A 5).map (diag (nodes A)) ≤ zeroSpace A 5) :
    15 ≤ s := dirk_uniform_of_invariant_middle_grade ha h (by decide) (by decide) (by decide) inv
example (h : HasOrder 12 A b) (short : s≤14) :
    ¬(zeroSpace A 6).map (diag (nodes A)) ≤ zeroSpace A 6 :=
  (dirk_short_forces_grade_six_band ha h (by decide) (by omega)).2 6 (by decide) (by decide)
end Field

section Ring
variable {R : Type u} [CommRing R] [CharZero R] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
example (ha : A.IsLowerTriangular) (h : HasOrder 12 A b)
    (g : ∀ (K : Type u) [Field K] [CharZero K] (T : Matrix (Fin s) (Fin s) K) (w : Fin s → K),
      T.IsLowerTriangular → HasOrder 12 T w →
        finrank K (zeroSpace T 3)+4 ≤ finrank K (zeroSpace T 6)) : 15 ≤ s :=
  h.dirk_charZero_count_of_field_grade_six ha (by decide) g
end Ring

#check dirk_order_twelve_of_grade_six
#check dirk_order_fifteen_of_grade_six
#check RKResearch.HasOrder.dirk_charZero_count_of_field_grade_six
#print axioms paid_unanchored_constant_cauchy
#print axioms dirk_reverse_room_unanchored
#print axioms dirk_even_marked_count
#print axioms dirk_odd_marked_count
#print axioms dirk_uniform_of_grade_six
#print axioms dirk_even_nonC2_of_grade_six
#print axioms dirk_order_twelve_of_grade_six
#print axioms dirk_order_thirteen_of_grade_six
#print axioms dirk_order_fifteen_of_grade_six
#print axioms RKResearch.HasOrder.dirk_charZero_count_of_field_grade_six
#print axioms dirk_uniform_of_invariant_middle_grade
#print axioms dirk_short_forces_grade_six_band
