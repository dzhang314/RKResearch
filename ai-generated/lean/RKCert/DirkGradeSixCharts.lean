module

public import RKCert.DirkRankBridge

@[expose] public section

/-! # Rank-saturated boundary charts fed by the grade-six payment

The hypotheses and conclusions concern the genuine original spaces. These
charts are prerequisites to (not proofs of) the strongest finite exclusions
at orders fourteen and fifteen. -/

namespace RKCert.Paired
open Module

variable {K : Type*} [Field K]

theorem dirk_chart14_of_grade6 {A : Fin 18 → Fin 18 → K} {b : Vec K 18}
    (ha : ∀ i j : Fin 18, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b 14)
    (h₆ : finrank K (zeroSpace A 3)+4≤finrank K (zeroSpace A 6)) :
    q₂ (mat A) (nodes A) 1=0 ∧ finrank K (zeroSpace A 3)=1 ∧
      finrank K (zeroSpace A 6)=5 ∧ finrank K (zeroSpace A 7)=6 ∧
      finrank K (treeSpace A 6)=12 ∧ finrank K (treeSpace A 7)=14 ∧
      ∃ i : Fin 18, b i≠0 ∧ nodes A i=1 ∧ Pi.single i (1:K)∈treeSpace A 7 := by
  have hcount := dirk_order14_of_grade6 ha ho h₆
  have hq : q₂ (mat A) (nodes A) 1=0 := by
    by_contra h
    have := hcount.2 h
    omega
  have h₃ := dirk_forward_rank_three ha ho (by decide)
  have h₀ := dirk_first_row ha hq
  have e6 := treeSpace_rank ho (q:=6) (by decide)
  have e7 := treeSpace_rank_of_separated A 7
    (poly_separated_of_first_row h₀ ho (m:=7) (by decide))
  have c6 := dirk_end_count_unanchored ha ho (m:=6) (r:=5) (by decide) (by decide)
  have c7 := dirk_end_count ha ho (m:=7) (r:=4) (by decide)
  have grow := Submodule.finrank_lt_finrank_of_lt (dirk_zeroSpace_lt_succ ha ho (j:=6)
    (by decide) (by decide))
  change finrank K (zeroSpace A 6)<finrank K (zeroSpace A 7) at grow
  exact ⟨hq,by omega,by omega,by omega,by omega,by omega,
    dirk_end_cardinal ha ho (m:=7) (r:=4) (by decide) (by omega)⟩

theorem dirk_chart15_origin_of_grade6 {A : Fin 20 → Fin 20 → K} {b : Vec K 20}
    (ha : ∀ i j : Fin 20, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b 15) (hq : q₂ (mat A) (nodes A) 1=0)
    (h₆ : finrank K (zeroSpace A 3)+4≤finrank K (zeroSpace A 6)) :
    finrank K (zeroSpace A 3)=1 ∧ finrank K (zeroSpace A 6)=5 ∧
      finrank K (zeroSpace A 7)=6 ∧ finrank K (treeSpace A 7)=14 := by
  have h₃ := dirk_forward_rank_three ha ho (by decide)
  have h₀ := dirk_first_row ha hq
  have e7 := treeSpace_rank_of_separated A 7
    (poly_separated_of_first_row h₀ ho (m:=7) (by decide))
  have c7 := dirk_end_count_anchor ha ho h₀ (m:=7) (r:=5) (by decide) (by decide)
  change finrank K (treeSpace A 7)+5+1 ≤ 20 at c7
  have grow := Submodule.finrank_lt_finrank_of_lt (dirk_zeroSpace_lt_succ ha ho (j:=6)
    (by decide) (by decide))
  change finrank K (zeroSpace A 6)<finrank K (zeroSpace A 7) at grow
  exact ⟨by omega,by omega,by omega,by omega⟩

theorem dirk_chart15_nonorigin_of_grade6 {A : Fin 20 → Fin 20 → K} {b : Vec K 20}
    (ha : ∀ i j : Fin 20, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b 15) (hq : q₂ (mat A) (nodes A) 1≠0)
    (h₆ : finrank K (zeroSpace A 3)+4≤finrank K (zeroSpace A 6)) :
    finrank K (zeroSpace A 3)=2 ∧ finrank K (zeroSpace A 6)=6 ∧
      finrank K (zeroSpace A 7)=7 ∧ finrank K (treeSpace A 6)=13 ∧
      finrank K (treeSpace A 7)=15 ∧
      ∃ i : Fin 20, b i≠0 ∧ nodes A i=1 ∧ Pi.single i (1:K)∈treeSpace A 7 := by
  have h₃ := dirk_forward_rank_three_nonzero ha ho (by decide) hq
  have e6 := treeSpace_rank ho (q:=6) (by decide)
  have e7 := treeSpace_rank ho (q:=7) (by decide)
  have c6 := dirk_end_count_unanchored ha ho (m:=6) (r:=6) (by decide) (by decide)
  have c7 := dirk_end_count ha ho (m:=7) (r:=5) (by decide)
  have grow := Submodule.finrank_lt_finrank_of_lt (dirk_zeroSpace_lt_succ ha ho (j:=6)
    (by decide) (by decide))
  change finrank K (zeroSpace A 6)<finrank K (zeroSpace A 7) at grow
  exact ⟨by omega,by omega,by omega,by omega,by omega,
    dirk_end_cardinal ha ho (m:=7) (r:=5) (by decide) (by omega)⟩

end RKCert.Paired
