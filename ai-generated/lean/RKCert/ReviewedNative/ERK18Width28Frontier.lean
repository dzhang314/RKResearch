module

public import RKCert.ReviewedNative.ERKCharZero
public import RKCert.ReviewedNative.ERKGradeEightSurplus

@[expose] public section

/-! # The measured order-eighteen width-28 frontier

The statements use the original tableau, its actual `zeroSpace`, and the
native reflected reverse flag.  They assert necessary alternatives only;
none excludes width 28. -/
namespace RKResearch.Certified.ERK18

open RKResearch Module RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse

section ReverseSeed
variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

theorem firstSeed_zero_iff_rank_zero :
    firstSeed A b = 0 ↔ finrank K (back A b 0) = 0 := by
  constructor
  · exact first_dim_zero
  · intro h
    classical
    by_contra z
    have h1 := first_dim_one z
    omega

end ReverseSeed

section MeasuredWidth
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- All three inequalities used by the census, without any width assumption. -/
theorem order18_measured_budget (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 18 A b) :
    9 ≤ finrank K (zeroSpace A 8) ∧
    finrank K (zeroSpace A 8) + 1 ≤ finrank K (zeroSpace A 9) ∧
    17 + finrank K (zeroSpace A 9) + finrank K (back A b 0) ≤ s := by
  have h8 := grade_eight_surplus_ordered_of_reviewed_order ha ho (by decide)
  have hg := erk_paid_rank_interval ha ho (a:=8) (q:=9)
    (by decide) (by decide) (by decide)
  have hb := erk_even_midpoint_budget ha ho (q:=9) (by decide) (by decide)
  exact ⟨h8, by simpa only [Nat.reduceSub] using hg,
    by simpa only [Nat.reduceMul,Nat.reduceSub] using hb⟩

/-- Restatement of the already earned floor, for the prefix argument only. -/
theorem order18_width_floor27_of_measured_budget (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 18 A b) : 27 ≤ s := by
  obtain ⟨h8,hg,hb⟩ := order18_measured_budget ha ho
  omega

end MeasuredWidth

section Count
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The 27-stage necessary rank equality, not an exclusion of that width. -/
theorem width27_actual_ranks {A : Matrix (Fin 27) (Fin 27) K} {b : Fin 27 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 18 A b) :
    finrank K (zeroSpace A 8) = 9 ∧ finrank K (zeroSpace A 9) = 10 ∧
      finrank K (back A b 0) = 0 := by
  obtain ⟨h8,hg,hb⟩ := order18_measured_budget ha ho
  exact ⟨by omega,by omega,by omega⟩

/-- Width 28 has precisely this arithmetic list of necessary alternatives.
The grade-eight rank is recorded as well as `(dim F9, r0)`. -/
theorem width28_actual_rank_frontier {A : Matrix (Fin 28) (Fin 28) K} {b : Fin 28 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 18 A b) :
    (finrank K (zeroSpace A 8) = 9 ∧ finrank K (zeroSpace A 9) = 10 ∧
       finrank K (back A b 0) = 0) ∨
    (finrank K (zeroSpace A 8) = 9 ∧ finrank K (zeroSpace A 9) = 10 ∧
       finrank K (back A b 0) = 1) ∨
    ((finrank K (zeroSpace A 8) = 9 ∨ finrank K (zeroSpace A 8) = 10) ∧
       finrank K (zeroSpace A 9) = 11 ∧ finrank K (back A b 0) = 0) := by
  obtain ⟨h8,hg,hb⟩ := order18_measured_budget ha ho
  by_cases ten : finrank K (zeroSpace A 9) = 10
  · have nine : finrank K (zeroSpace A 8) = 9 := by omega
    by_cases z : finrank K (back A b 0) = 0
    · exact Or.inl ⟨nine,ten,z⟩
    · exact Or.inr (Or.inl ⟨nine,ten,by omega⟩)
  · have eleven : finrank K (zeroSpace A 9) = 11 := by omega
    have f8 : finrank K (zeroSpace A 8) = 9 ∨ finrank K (zeroSpace A 8) = 10 := by
      by_cases h : finrank K (zeroSpace A 8) = 9
      · exact Or.inl h
      · exact Or.inr (by omega)
    exact Or.inr (Or.inr ⟨f8,eleven,by omega⟩)

end Count

section ReverseRoom
variable {K : Type*} [Field K]
variable {A : Matrix (Fin 28) (Fin 28) K} {b : Fin 28 → K}

theorem width28_midpoint_annihilator_rank (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 18 A b) :
    10 + finrank K (zeroSpace A 9) + finrank K (annih (treeSpace A 9)) = 28 := by
  have h := erk_midpoint_tree_rank ha ho (q:=9) (by decide) (by decide)
  have amb := finrank_annih (treeSpace A 9)
  rw [Fintype.card_fin, h] at amb
  exact amb

/-- The last paid reverse space is grade 7, because `9+7+2=18`. -/
theorem width28_reverse_grade7_room (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 18 A b) :
    finrank K (back A b 0) + 7 ≤ finrank K (back A b 7) ∧
    finrank K (back A b 7) ≤ finrank K (primitiveBack A b 7) ∧
    finrank K (primitiveBack A b 7) + finrank K (zeroSpace A 9) ≤ 18 := by
  have lo := back_finrank ha ho 7 (by decide)
  have mid := Submodule.finrank_mono (back_le_primitiveBack (A:=A) (b:=b) 7)
  have hi := Submodule.finrank_mono (primitiveBack_annih ho 9 7 (by decide))
  have amb := width28_midpoint_annihilator_rank ha ho
  exact ⟨lo,mid,by omega⟩

/-- Exact flags in either saturated case `(10,1)` or `(11,0)`.
This argument does not assume a zero initial seed. -/
theorem width28_saturated_reverse_flag (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 18 A b)
    (sat : 17 + finrank K (zeroSpace A 9) + finrank K (back A b 0) = 28) :
    back A b 7 = annih (treeSpace A 9) ∧
    primitiveBack A b 7 = annih (treeSpace A 9) ∧
    (∀ n ≤ 7, finrank K (back A b n) = finrank K (back A b 0) + n ∧
      back A b n = primitiveBack A b n) := by
  have amb := width28_midpoint_annihilator_rank ha ho
  have lo := back_finrank ha ho 7 (by decide)
  have full : back A b 7 = annih (treeSpace A 9) :=
    Submodule.eq_of_le_of_finrank_le (back_annih ho 9 7 (by decide)) (by omega)
  have pfull : primitiveBack A b 7 = annih (treeSpace A 9) := by
    apply le_antisymm (primitiveBack_annih ho 9 7 (by decide))
    rw [← full]
    exact back_le_primitiveBack 7
  have top : finrank K (primitiveBack A b 7) = finrank K (back A b 0) + 7 := by
    rw [pfull]
    omega
  refine ⟨full,pfull,?_⟩
  intro n hn
  have gain := primitiveBack_interval ha ho n (7-n) (by omega)
  rw [show n+(7-n)=7 by omega,top] at gain
  have lower := back_finrank ha ho n (by omega)
  have inc := back_le_primitiveBack (A:=A) (b:=b) n
  have mid := Submodule.finrank_mono inc
  exact ⟨by omega,Submodule.eq_of_le_of_finrank_le inc (by omega)⟩

end ReverseRoom
end RKResearch.Certified.ERK18
