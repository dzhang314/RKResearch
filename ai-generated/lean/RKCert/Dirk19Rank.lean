module
public import RKCert.Dirk15RankChart
public import RKCert.DirkTenShortMask
public import RKCert.DirkPaidTailDual
@[expose] public section
namespace RKCert.Paired.Nineteen
open Module Terminal
variable {K:Type*} [Field K] [CharZero K] {A:Fin 26→Fin 26→K} {b:Vec K 26}

noncomputable def excess (A:Fin 26→Fin 26→K) : ℕ := by
  classical exact if q₂ (mat A) (nodes A) 1=0 then 0 else 1

structure Ranks (A:Fin 26→Fin 26→K) : Prop where
  f3 : finrank K (zeroSpace A 3)=1+excess A
  f5_upper : finrank K (zeroSpace A 5)≤4+excess A
  f6 : finrank K (zeroSpace A 6)=5+excess A
  f8 : finrank K (zeroSpace A 8)=7+excess A
  f9 : finrank K (zeroSpace A 9)=8+excess A
  f10 : finrank K (zeroSpace A 10)=10+excess A
  e9 : finrank K (treeSpace A 9)=18+excess A
  e10 : finrank K (treeSpace A 10)=20
  e9_full : treeSpace A 9=LinearMap.range (polyEval A 9) ⊔zeroSpace A 9
  e10_full : treeSpace A 10=LinearMap.range (polyEval A (9-excess A)) ⊔zeroSpace A 10

theorem initial_ranks (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 19) : Ranks A:=by
  classical
  have f3:=dirk_forward_rank_three ha ho (by decide)
  have f6:=dirk_grade_six_surplus ha ho (by decide)
  have f8:=flag_gain ha ho (a:=6) (n:=8) (by decide) (by decide) (by decide)
  have f9:=flag_gain ha ho (a:=8) (n:=9) (by decide) (by decide) (by decide)
  have f10:=grade_three_ten_surplus ha ho (by decide)
  have f5:=grade_five_ten_surplus ha ho (by decide)
  have eq9:=treeSpace_rank ho (q:=9) (by decide)
  have cap9:=dirk_end_count ha ho (m:=9) (r:=7) (by decide)
  have cap10:=dirk_end_count ha ho (m:=10) (r:=6) (by decide)
  have E9full : treeSpace A 9=LinearMap.range (polyEval A 9) ⊔zeroSpace A 9:=by
    apply le_antisymm _ (sup_le (by rintro _ ⟨a,rfl⟩;exact polyEval_mem_treeSpace A _ a) (zeroSpace_le_treeSpace A _))
    intro f hf
    obtain ⟨a,pa⟩:=exists_poly_zeroSpace ho (by decide : 9+1≤19) hf
    exact (Submodule.mem_sup.mpr ⟨_,⟨a,rfl⟩,_,pa,by abel⟩)
  by_cases h:q₂ (mat A) (nodes A) 1=0
  · have ex:excess A=0:=by simp [excess,h]
    have origin:=dirk_first_row ha h
    have sep:∀a:Fin 10→K,polyEval A 9 a∈zeroSpace A 10→a=0:=poly_separated_delayed_first origin ho (q:=9) (m:=10) (by decide) (by decide)
    have lower:=treeSpace_rank_of_delayed (by decide:9≤10) sep
    have anc:=dirk_end_count_anchor (s:=25) ha ho origin (m:=9) (r:=7) (by decide) (by decide)
    change finrank K (treeSpace A 9)+8≤26 at anc
    have eFull:=poly_pure_full_of_paid_rank (by decide:9≤10) sep (by omega)
    constructor <;> (try rw [ex]) <;> first | exact E9full | exact eFull | omega
  · have ex:excess A=1:=by simp [excess,h]
    have two:=dirk_forward_rank_three_nonzero ha ho (by decide) h
    have sep:=poly_separated_delayed ho (q:=8) (m:=10) (by decide) (by decide)
    have lower:=treeSpace_rank_of_delayed (by decide:8≤10) sep
    have eFull:=poly_pure_full_of_paid_rank (by decide:8≤10) sep (by omega)
    constructor <;> (try rw [ex]) <;> first | exact E9full | exact eFull | omega

/-- Any stage trailing a zero output can be trimmed without changing the
classical order. The order-19 parity floor therefore pays its last weight. -/
theorem terminal_weight (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 19) : b (Fin.last 25)≠0:=by
  intro hb
  let h:25≤26:=by decide
  have trimmed:=order_on_lower_prefix ha ho h (fun i hi=>by
    have e:i=Fin.last 25:=Fin.ext (by simp only [Fin.val_last];have:=i.isLt;omega)
    rwa [e])
  have bad:=odd_floor (m:=9) (by decide) (lower_prefix ha h) trimmed
  omega

end RKCert.Paired.Nineteen
