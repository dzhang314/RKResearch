module
public import RKCert.DirkGradeSix
@[expose] public section
namespace RKCert.Paired.Terminal
open Module
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ} {A : Fin s → Fin s → K} {b : Vec K s}

omit [CharZero K] in
theorem flag_gain (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p)
    {a n:ℕ} (ha' : 2≤a) (han:a≤n) (hp:n≤p) :
    finrank K (zeroSpace A a)+(n-a)≤finrank K (zeroSpace A n) := by
  induction n, han using Nat.le_induction with
  | base => simp
  | succ n h ih =>
    have hprev:=ih (by omega)
    have hnext:=Submodule.finrank_lt_finrank_of_lt
      (dirk_zeroSpace_lt_succ ha ho (j:=n) (by omega) (by omega))
    omega

/-- Cost of the grade-six surplus at a later grade of the true tableau. -/
theorem floor_later (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p) {n:ℕ}
    (hp:8≤p) (h6:6≤n) (hn:n≤p) :
    finrank K (zeroSpace A 3) + (n-2) ≤ finrank K (zeroSpace A n) := by
  have h:=dirk_grade_six_surplus ha ho hp
  have hl:=flag_gain ha ho (a:=6) (by decide) h6 hn
  omega

/-- Every even full order in the supported range pays three stages per two
additional orders; the non-C(2) family pays one further physical stage. -/
theorem even_floor {m:ℕ} (hm:7≤m) (ha:LowerArray A)
    (ho:HasTreeOrderAtLeast A b (2*m)) :
    3*m≤s+3 ∧ (q₂ (mat A) (nodes A) 1≠0 → 3*m≤s+2) := by
  have base:=dirk_forward_rank_three ha ho (by omega)
  have prev:=floor_later ha ho (n:=m-1) (by omega) (by omega) (by omega)
  have old:=treeSpace_rank ho (q:=m-1) (by omega)
  have ec:=dirk_end_count_unanchored ha ho (m:=m-1) (r:=m-2) (by omega) (by omega)
  have non (hq:q₂ (mat A) (nodes A) 1≠0) : 3*m≤s+2 := by
    have hn:=dirk_forward_rank_three_nonzero ha ho (by omega) hq
    omega
  refine ⟨?_,non⟩
  by_cases hq:q₂ (mat A) (nodes A) 1=0
  · cases s with
    | zero => omega
    | succ s =>
      have origin:=dirk_first_row ha hq
      have em:=treeSpace_rank_of_separated A m
        (poly_separated_of_first_row origin ho (m:=m) (by omega))
      have final:=dirk_end_count ha ho (m:=m) (r:=m-3) (by omega)
      have mid:=floor_later ha ho (n:=m) (by omega) (by omega) (by omega)
      omega
  · have := non hq; omega

/-- Odd-order native floor. The two cases use different earned terminal
moment rows, so the right-hand side does not assume a zero first row. -/
theorem odd_floor {m:ℕ} (hm:7≤m) (ha:LowerArray A)
    (ho:HasTreeOrderAtLeast A b (2*m+1)) : 3*m≤s+1 := by
  have base:=dirk_forward_rank_three ha ho (by omega)
  have prev:=floor_later ha ho (n:=m-1) (by omega) (by omega) (by omega)
  have old:=treeSpace_rank ho (q:=m-1) (by omega)
  have ec:=dirk_end_count_unanchored ha ho (m:=m-1) (r:=m-1) (by omega) (by omega)
  by_cases hq:q₂ (mat A) (nodes A) 1=0
  · cases s with
    | zero => omega
    | succ s =>
      have origin:=dirk_first_row ha hq
      have mid:=floor_later ha ho (n:=m) (by omega) (by omega) (by omega)
      have em:=treeSpace_rank ho (q:=m) (by omega)
      have final:=dirk_end_count_anchor ha ho origin (m:=m) (r:=m-2) (by omega) (by omega)
      omega
  · have hn:=dirk_forward_rank_three_nonzero ha ho (by omega) hq
    omega

end RKCert.Paired.Terminal

namespace RKCert.Paired
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ} {A : Fin s → Fin s → K} {b : Vec K s}

/-- The current unrestricted characteristic-zero order-17 lower bound.
No ordering or reality assumptions enter this 23-stage result. -/
theorem dirk_order17_charZero_field (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p)
    (hp : 17≤p) : 23≤s := by
  have h17 : HasTreeOrderAtLeast A b 17 := fun t h => ho t (h.trans hp)
  have h:=Terminal.odd_floor (m:=8) (by decide) ha h17
  omega
end RKCert.Paired

namespace RKCert
universe u
variable {R : Type u} [CommRing R] [CharZero R] {s m : ℕ}
variable {A : Fin s → Fin s → R} {b : Fin s → R}

/-- Even native floor after characteristic-zero prime specialization. -/
theorem dirk_even_native_ring (hm:7≤m)
    (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b (2*m)) : 3*m-3≤s := by
  apply lowerTriangular_of_charZero_fields (A:=A) (b:=b) (p:=2*m) _ ha ho
  intro K _ _ a β ht hs
  have hh := (Paired.Terminal.even_floor hm ht hs).1
  omega

/-- Odd native floor, including the characteristic-zero order-17 bound 23. -/
theorem dirk_odd_native_ring (hm:7≤m)
    (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b (2*m+1)) : 3*m-1≤s := by
  apply lowerTriangular_of_charZero_fields (A:=A) (b:=b) (p:=2*m+1) _ ha ho
  intro K _ _ a β ht hs
  have hh := Paired.Terminal.odd_floor hm ht hs
  omega

theorem dirk_order17_charZero_ring {p:ℕ}
    (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) (hp:17≤p) : 23≤s :=
  lowerTriangular_of_charZero_fields
    (fun _ _ _ _ _ ht hs => Paired.dirk_order17_charZero_field ht hs hp) ha ho

end RKCert
