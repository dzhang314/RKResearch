module
public import RKCert.ReviewedNative.OrderNineReverseChart
public import RKCert.ReviewedNative.OneOffWideProfiles

@[expose] public section

/-! # Actual order-nine rank-five terminal coordinate and native defect payment -/
namespace RKResearch.Certified.Graded.OneOff
open Module RKResearch
open scoped Matrix Classical

variable {K : Type*} [Field K] {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12 → K}

theorem order9_grade_five_upper (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 9 A b) : finrank K (treeSpace A 5) ≤ 10 := by
  have h := Reverse.backward_count ha ho 5 2 (by decide)
  omega

theorem order9_grade_six_upper (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 9 A b) : finrank K (treeSpace A 6) ≤ 11 := by
  have h := Reverse.backward_count ha ho 6 1 (by decide)
  omega

/-- A maximally ranked grade-five space contains the live physical
terminal coordinate, but it is not a grade-four column. -/
theorem order9_rank_five_full_terminal (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 9 A b) (rank : finrank K (treeSpace A 5) = 10) :
    b (Fin.last 11) ≠ 0 ∧ nodes A (Fin.last 11) = 1 ∧
      Reverse.coordinate (K:=K) (Fin.last 11) ∈ treeSpace A 5 ∧
      Reverse.coordinate (K:=K) (Fin.last 11) ∉ treeSpace A 4 := by
  have term := Reverse.lastActive_of_odd_floor ha ho (q:=4) (by decide) (by decide) (by decide)
  obtain ⟨_,one,v5,v4,_,_⟩ := Reverse.orderNine_rank_five_full ha ho rank
  exact ⟨term.live,one,v5,v4⟩

/-- At full grade-five rank, third-grade defects vanish at the actual
last coordinate. This uses exactly the grade-three times grade-five budget. -/
theorem rank_five_full_terminal_defect (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 9 A b) (rank : finrank K (treeSpace A 5) = 10)
    {u : Fin 12 → K} (hu : u ∈ zeroSpace A 3) : u (Fin.last 11) = 0 := by
  obtain ⟨hb,_,e,_⟩ := order9_rank_five_full_terminal ha ho rank
  let j : Fin 12 := Fin.last 11
  let w : Fin 12 → K := Reverse.coordinate j
  have hm : u*w ∈ zeroSpace A (3+5) := zeroSpace_mul_treeSpace ho (by decide : 5+1≤9) hu e
  have p : probe A b 0 (u*w) = 0 := probe_zeroSpace ho (k:=0) (by decide) hm
  have e1 : u*w = (u j) • w := by
    ext l
    by_cases h : l=j
    · simp [w,Reverse.coordinate,h]
    · simp [w,Reverse.coordinate,h]
  have wb : probe A b 0 w = b j := by
    change row _ (Reverse.coordinate j) = _
    rw [Reverse.row_coordinate,pow_zero,mul_one]
  rw [e1,map_smul,smul_eq_mul,wb] at p
  exact (mul_eq_zero.mp p).resolve_right hb

end RKResearch.Certified.Graded.OneOff
