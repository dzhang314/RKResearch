module
public import RKCert.DirkTwentyRanks
public import RKCert.DirkTenShortMask
@[expose] public section
namespace RKCert.Paired.Terminal
open Module
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ}
noncomputable section

theorem twenty_floor_from_grade_ten {A:Fin s→Fin s→K} {b:Vec K s}
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20):28≤s:=by
  cases s with
  | zero=>
    obtain ⟨t,_,_⟩:=last_output ho (by decide)
    exact t.elim0
  | succ s=>
    have front:=twenty_midpoint_21 ha ho (grade_three_ten_surplus ha ho (by decide))
    have endp:=dirk_end_count ha ho (m:=10) (r:=7) (by decide)
    omega

variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

theorem twenty_ranks (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20) (size:s+1=28) :
    ∃e,TwentyRanks A b e :=
  twenty_rank_of_paid ha ho size (grade_three_ten_surplus ha ho (by decide))

/-- The actual last physical output is paid; its column is zero, its
cardinal is in E10, and every F9 (not necessarily F10) vector is zero there. -/
theorem twenty_final_row (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20) (size:s+1=28)
    {e:ℕ} (h:TwentyRanks A b e) :
    b (Fin.last s)≠0 ∧ nodes A (Fin.last s)=1 ∧
    (∀i,A i (Fin.last s)=0) ∧ Pi.single (Fin.last s) (1:K)∈treeSpace A 10 ∧
    ∀f∈zeroSpace A 9,f (Fin.last s)=0:=by
  classical
  let t:=Fin.last s
  have hb:b t≠0:=by
    intro z
    have short:s≤s+1:=by omega
    have all (i:Fin (s+1)) (hi:s ≤ i.val):b i=0:=by
      have last:i=t:=Fin.ext (by have:=i.isLt;change i.val=s;omega)
      simpa [last] using z
    have cnt:=twenty_floor_from_grade_ten (lower_prefix ha short) (order_on_lower_prefix ha ho short all)
    omega
  have after(j:Fin (s+1))(later:t<j):b j=0:=False.elim ((not_lt_of_ge (Fin.le_last j)) later)
  obtain ⟨d1,d2⟩:=h.seeds
  have hy:=dirk_last_node ha t hb after d1 d2
  have ht:nodes A t=1:=(sub_eq_zero.mp (show 1-nodes A t=0 from hy)).symm
  have dg:A t t=0:=by
    have eqn:=congrFun d1 t
    change transMat A b t-mirror A t*b t=0 at eqn
    rw [causalDiag_transpose ha t b (fun j hj=>after j (Fin.rev_lt_rev.mp hj)),hy,zero_mul,sub_zero] at eqn
    exact (mul_eq_zero.mp eqn).resolve_right hb
  have col(i:Fin (s+1)):A i t=0:=by
    rcases lt_or_eq_of_le (Fin.le_last i) with lt|eq
    · exact ha i t lt
    · simpa [eq,t] using dg
  have card:Pi.single t (1:K)∈treeSpace A 10:=by
    rw [(h.dual 10 7 (by decide) (by decide)).2.2.2,mem_annih]
    intro v hv
    have z:v t=0:=dirkBack_prior ha t after hy d1 d2 7 hv t (show t≤t from le_rfl)
    simp [row_apply,Pi.single_apply,z]
  exact ⟨hb,ht,col,card,cardinal_clean_lower ho (j:=9) (by decide) t hb card⟩

end
end RKCert.Paired.Terminal

