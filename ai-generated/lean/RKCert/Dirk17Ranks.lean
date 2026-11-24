module
public import RKCert.DirkFourEightSurplus
public import RKCert.DirkTenShortMask
public import RKCert.DirkPaidTailDual
@[expose] public section
namespace RKCert.Paired.Seventeen
open Module Terminal RKCert.EndpointPhysical
variable {K:Type*} [Field K] [CharZero K] {A:Fin 23→Fin 23→K} {b:Vec K 23}
noncomputable def excess (A:Fin 23→Fin 23→K):ℕ:=by
  classical exact if q₂ (mat A) (nodes A) 1=0 then 0 else 1

structure Ranks (A:Fin 23→Fin 23→K):Prop where
  three:finrank K (zeroSpace A 3)=1+excess A
  five:3+excess A≤finrank K (zeroSpace A 5) ∧ finrank K (zeroSpace A 5)≤4+excess A
  six:finrank K (zeroSpace A 6)=5+excess A
  seven:finrank K (zeroSpace A 7)=6+excess A
  eight:finrank K (zeroSpace A 8)=7+excess A
  nine:8+excess A≤finrank K (zeroSpace A 9) ∧ finrank K (zeroSpace A 9)≤9+excess A
  ten:10+excess A≤finrank K (zeroSpace A 10) ∧ finrank K (zeroSpace A 10)≤11+excess A
  eleven:finrank K (zeroSpace A 11)≤13+excess A
  e8:finrank K (treeSpace A 8)=16+excess A
  e8_full:treeSpace A 8=LinearMap.range (polyEval A 8) ⊔ zeroSpace A 8

/-- Both numerical C(2) branches through ordinary and tree grade eight
before imposing any ordering (or square-root) assumption. -/
theorem ranks (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17):Ranks A:=by
  classical
  have f3:=dirk_forward_rank_three ha ho (by decide)
  have f6:=dirk_grade_six_surplus ha ho (by decide)
  have a:=flag_gain ha ho (a:=3) (n:=5) (by decide) (by decide) (by decide)
  have b5:=flag_gain ha ho (a:=5) (n:=6) (by decide) (by decide) (by decide)
  have b6:=flag_gain ha ho (a:=6) (n:=7) (by decide) (by decide) (by decide)
  have b7:=flag_gain ha ho (a:=7) (n:=8) (by decide) (by decide) (by decide)
  have b8:=flag_gain ha ho (a:=8) (n:=9) (by decide) (by decide) (by decide)
  have t:=grade_three_ten_surplus ha ho (by decide)
  have e8:=treeSpace_rank ho (q:=8) (by decide)
  have c8:=dirk_end_count ha ho (m:=8) (r:=6) (by decide)
  have c9:=dirk_end_count ha ho (m:=9) (r:=5) (by decide)
  have c10:=dirk_end_count ha ho (m:=10) (r:=4) (by decide)
  have c11:=dirk_end_count ha ho (m:=11) (r:=3) (by decide)
  have E:treeSpace A 8=LinearMap.range (polyEval A 8) ⊔ zeroSpace A 8:=by
    apply le_antisymm _ (sup_le (by rintro _ ⟨x,rfl⟩;exact polyEval_mem_treeSpace A _ x) (zeroSpace_le_treeSpace A _))
    intro f hf
    obtain ⟨x,hx⟩:=exists_poly_zeroSpace ho (by decide:8+1≤17) hf
    exact Submodule.mem_sup.mpr ⟨_,⟨x,rfl⟩,_,hx,by abel⟩
  by_cases h:q₂ (mat A) (nodes A) 1=0
  · have z:excess A=0:=by simp [excess,h]
    have org:=dirk_first_row ha h
    have cap:=dirk_end_count_anchor (s:=22) ha ho org (m:=8) (r:=6) (by decide) (by decide)
    have r9:=treeSpace_rank_of_delayed (by decide:8≤9) (poly_separated_delayed_first org ho (q:=8) (m:=9) (by decide) (by decide))
    have r10:=treeSpace_rank_of_delayed (by decide:7≤10) (poly_separated_delayed_first org ho (q:=7) (m:=10) (by decide) (by decide))
    have r11:=treeSpace_rank_of_delayed (by decide:6≤11) (poly_separated_delayed_first org ho (q:=6) (m:=11) (by decide) (by decide))
    change finrank K (treeSpace A 8)+7≤23 at cap
    change 9+finrank K (zeroSpace A 9)≤finrank K (treeSpace A 9) at r9
    change 8+finrank K (zeroSpace A 10)≤finrank K (treeSpace A 10) at r10
    change 7+finrank K (zeroSpace A 11)≤finrank K (treeSpace A 11) at r11
    constructor <;> (try rw [z]) <;> first
      | exact E
      | (constructor <;> omega)
      | omega
  · have z:excess A=1:=by simp [excess,h]
    have plus:=dirk_forward_rank_three_nonzero ha ho (by decide) h
    have r9:=treeSpace_rank_of_delayed (by decide:7≤9) (poly_separated_delayed ho (q:=7) (m:=9) (by decide) (by decide))
    have r10:=treeSpace_rank_of_delayed (by decide:6≤10) (poly_separated_delayed ho (q:=6) (m:=10) (by decide) (by decide))
    have r11:=treeSpace_rank_of_delayed (by decide:5≤11) (poly_separated_delayed ho (q:=5) (m:=11) (by decide) (by decide))
    constructor <;> (try rw [z]) <;> first
      | exact E
      | (constructor <;> omega)
      | omega

/-- The exact grade-four rank needs only exclusion of sqrt(-6), not a
chosen ordering or an embedding in the real numbers. -/
theorem rank_four (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17) (field:NoExceptionalRatio K):
    finrank K (zeroSpace A 4)=2+excess A:=by
  have R:=ranks ha ho;have lo:=R.three;have cap:=R.eight
  have g:=flag_gain ha ho (a:=3) (n:=4) (by decide) (by decide) (by decide)
  have h:=grade_four_eight_surplus ha ho (by decide) field
  omega
end RKCert.Paired.Seventeen
