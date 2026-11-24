module
public import RKCert.DirkEvenBoundary
@[expose] public section
namespace RKCert.Paired.Terminal
open Module
variable {K : Type*} [Field K] [CharZero K] {s p m:ℕ} {A : Fin s→Fin s→K} {b : Vec K s}

omit [CharZero K] in
theorem tree_flag_gain (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    {a n:ℕ} (han:a≤n) (hp:n+3≤p) :
    finrank K (treeSpace A a)+(n-a)≤finrank K (treeSpace A n) := by
  induction n, han using Nat.le_induction with
  | base => simp
  | succ n h ih =>
    have hprev:=ih (by omega)
    have hnext:=Submodule.finrank_lt_finrank_of_lt
      (dirk_treeSpace_lt_succ ha ho (j:=n) (by omega))
    omega

variable {T : Fin (s+1)→Fin (s+1)→K} {β : Vec K (s+1)}

/-- The entire tail of the actual untrimmed tree and adjoint-word flags is
mutually annihilating with complementary dimensions. The output row enters
through genuine moment annihilation, not a synthetic transposed tableau. -/
theorem even_dual_band (hm:7≤m) (ha:LowerArray T)
    (ho:HasTreeOrderAtLeast T β (2*m)) (he:s+1+3=3*m) {q r:ℕ}
    (hq:m≤q) (hr:q+r+3=2*m) :
    finrank K (treeSpace T q)=m+q ∧ finrank K (dirkBack T β r)=r ∧
    dirkBack T β r=annih (treeSpace T q) ∧ treeSpace T q=annih (dirkBack T β r) := by
  obtain ⟨_,_,_,_,_,em,_⟩:=even_boundary hm ha ho he
  have tail:=tree_flag_gain ha ho hq (by omega)
  have back:=dirkBack_rank ha ho r (by omega)
  have an:=dirkBack_annih ho q r (by omega)
  have pay:=finrank_annih_le an
  have flip:=annih_flip_le an
  have ar:=finrank_annih_le (le_refl (annih (treeSpace T q)))
  have ae:=finrank_annih_le (le_refl (annih (dirkBack T β r)))
  exact ⟨by omega,by omega,Submodule.eq_of_le_of_finrank_le an (by omega),
    Submodule.eq_of_le_of_finrank_le flip (by omega)⟩

theorem even_zero_reverse_seeds (hm:7≤m) (ha:LowerArray T)
    (ho:HasTreeOrderAtLeast T β (2*m)) (he:s+1+3=3*m) :
    backSeed1 T β=0 ∧ q₂ (transMat T) (mirror T) β=0 := by
  have h:=even_dual_band hm ha ho he (q:=2*m-3) (r:=0) (by omega) (by omega)
  exact twoOrbit_initial_zero h.2.1

end RKCert.Paired.Terminal
