module

public import RKCert.DirkFiveCommon
public import RKCert.FourDebutComplete
public import RKCert.DirkGradeSixCharts
public import RKCert.CharZeroTransfer

@[expose] public section

/-! # Characteristic-zero unrestricted DIRK through the sixth grade

Both genuine branches of a unit rank band are impossible. This composes
the finite-grade chronological projection and five-donor jet contradiction
with the native four-debut invariant-head exclusion. No row anchoring, weight
sign, clock ordering, or nonzero individual diagonal is required. -/

namespace RKCert.Paired
open RKCert.Paired.Clock Module

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Fin s → Fin s → K} {b : Vec K s}

/-- Among the three native ordinary rank increases from grade three through
six, at least one costs an extra dimension. -/
theorem dirk_grade_six_surplus (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p)
    (hp : 8≤p) :
    finrank K (zeroSpace A 3)+4≤finrank K (zeroSpace A 6) := by
  by_contra hbad
  by_cases hinv : (zeroSpace A 3).map (diag (nodes A))≤zeroSpace A 3
  · obtain ⟨w,hU,_,hband⟩ := dirk_six_head_starts_at_four ha ho hp hbad hinv
    exact RKCert.FourDebut.no_grade4_head ha ho hp hinv hU le_rfl hband
  · obtain ⟨U,w,P,hHead⟩ := grade3_head_if_noninvariant ha ho hp hbad hinv
    exact Reduce.no_grade3_head hHead ha ho hp

/-- The attained order-12 floor over every characteristic-zero field. -/
theorem dirk_order12_charZero_field (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p)
    (hp : 12≤p) : 15≤s := by
  have ht : HasTreeOrderAtLeast A b 12 := fun t h => ho t (h.trans hp)
  exact dirk_order12_of_grade6 ha ht (dirk_grade_six_surplus ha ho (by omega))

/-- The attained order-13 floor over every characteristic-zero field. -/
theorem dirk_order13_charZero_field (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p)
    (hp : 13≤p) : 17≤s := by
  have ht : HasTreeOrderAtLeast A b 13 := fun t h => ho t (h.trans hp)
  exact dirk_order13_of_grade6 ha ht (dirk_grade_six_surplus ha ho (by omega))

/-- Native order-14 rank prerequisite. The strongest unrestricted finite
exclusion at this order is separate. -/
theorem dirk_order14_native_rank (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 14) :
    18≤s ∧ (q₂ (mat A) (nodes A) 1≠0 → 19≤s) :=
  dirk_order14_of_grade6 ha ho (dirk_grade_six_surplus ha ho (by decide))

/-- Native order-15 rank prerequisite. It is strictly weaker than the
separate strongest finite integer stage exclusion. -/
theorem dirk_order15_native_rank (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15) :
    20≤s :=
  dirk_order15_of_grade6 ha ho (dirk_grade_six_surplus ha ho (by decide))

end RKCert.Paired

namespace RKCert
universe u
variable {R : Type u} [CommRing R] [CharZero R] {s p : ℕ}
variable {A : Fin s → Fin s → R} {b : Fin s → R}

/-- No order, reducedness, domain, or torsion-free additive group is assumed
of the coefficient ring. Prime specialization preserves characteristic zero. -/
theorem dirk_order12_charZero_ring
    (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) (hp : 12≤p) : 15≤s :=
  lowerTriangular_of_charZero_fields
    (fun _ _ _ _ _ ht hs => Paired.dirk_order12_charZero_field ht hs hp) ha ho

theorem dirk_order13_charZero_ring
    (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) (hp : 13≤p) : 17≤s :=
  lowerTriangular_of_charZero_fields
    (fun _ _ _ _ _ ht hs => Paired.dirk_order13_charZero_field ht hs hp) ha ho

end RKCert
