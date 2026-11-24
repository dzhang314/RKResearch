module
public import RKCert.DirkParityFloor
public import RKCert.TerminalClean
public import RKCert.DirkHermite
@[expose] public section
namespace RKCert.Paired.Terminal
open Module
variable {K : Type*} [Field K] [CharZero K] {s m:ℕ} {A : Fin (s+1)→Fin (s+1)→K}
variable {b : Vec K (s+1)}

/-- Structural equality case of the all-order even DIRK floor. The terminal
row below is an earned, output-active physical coordinate; no physical or
zero-weight row is removed. Both terminal zeros are deduced, not assumed. -/
theorem even_boundary (hm:7≤m) (ha:LowerArray A)
    (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m) :
    (∀j, A 0 j=0) ∧ finrank K (zeroSpace A 3)=1 ∧ finrank K (zeroSpace A 6)=5 ∧
    finrank K (zeroSpace A (m-1))=m-2 ∧ finrank K (zeroSpace A m)=m-1 ∧
    finrank K (treeSpace A m)=2*m ∧
    ∃t:Fin (s+1), b t≠0 ∧ nodes A t=1 ∧ Pi.single t (1:K)∈treeSpace A m ∧
      (∀f∈zeroSpace A (m-1), f t=0) ∧ (∀f∈zeroSpace A m, f t=0) := by
  have no: q₂ (mat A) (nodes A) 1=0 := by
    by_contra hn
    have h:=(even_floor hm ha ho).2 hn
    omega
  have origin:=dirk_first_row ha no
  have hb:=dirk_forward_rank_three ha ho (by omega)
  have six:=dirk_grade_six_surplus ha ho (by omega)
  have p6:=floor_later ha ho (n:=m-1) (by omega) (by omega) (by omega)
  have pprev:=flag_gain ha ho (a:=6) (n:=m-1) (by decide) (by omega) (by omega)
  have plus:=flag_gain ha ho (a:=m-1) (n:=m) (by omega) (by omega) (by omega)
  have em:=treeSpace_rank_of_separated A m (poly_separated_of_first_row origin ho (m:=m) (by omega))
  have count:=dirk_end_count ha ho (m:=m) (r:=m-3) (by omega)
  obtain ⟨t,hbt,hct,card⟩:=dirk_end_cardinal ha ho (m:=m) (r:=m-3) (by omega) (by omega)
  have prev:=cardinal_clean_lower ho (j:=m-1) (by omega) t hbt card
  have jm:m-1+1=m := by omega
  have one:finrank K (zeroSpace A (m-1+1))≤finrank K (zeroSpace A (m-1))+1 := by rw [jm]; omega
  have esc:¬ (zeroSpace A (m-1)).map (diag (nodes A))≤zeroSpace A (m-1) := by
    intro hh
    have h:=dirk_forward_invariant_outgoing ha ho (j:=m-1) (by omega) (zeroSpace A (m-1))
      le_rfl (fun v hv => hh ⟨v,hv,rfl⟩)
    rw [jm] at h
    omega
  have clean:=clean_next_of_escape t prev one esc
  rw [jm] at clean
  exact ⟨origin,by omega,by omega,by omega,by omega,by omega,t,hbt,hct,card,prev,clean⟩

end RKCert.Paired.Terminal
