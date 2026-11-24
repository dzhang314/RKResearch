module
public import RKCert.DirkEvenMarked
public import RKCert.DirkReverseHermite
@[expose] public section
namespace RKCert.Paired.Terminal
open Module RKCert.OneEscape
variable {K : Type*} [Field K] [CharZero K] {s m:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
noncomputable section

abbrev tau (A:Fin (s+1)→Fin (s+1)→K) (b:Vec K (s+1)) :=
  q₃ (transMat A) (mirror A) b

theorem word_rank (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) {r:ℕ} (hr:r≤m-2) : finrank K (dirkBack A b r)=r := by
  by_cases h:r=m-2
  · subst r
    obtain ⟨_,_,_,_,_,_,h,_⟩:=true_terminal_zero_band hm ha ho he
    exact h
  · exact (even_dual_band hm ha ho he (q:=2*m-r-3) (r:=r) (by omega) (by omega)).2.1

theorem zeroMarked_eq_words (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) {j:ℕ} (lo:2≤j) (hj:j≤m) :
    ReverseHermite.zeroMarked A (2*m) (Fin.last s) j=dirkBack A b (j-2) := by
  obtain ⟨_,ct,_⟩:=last_physical hm ha ho he
  obtain ⟨h1,h2⟩:=even_zero_reverse_seeds hm ha ho he
  have hb (i:Fin (s+1)) (hlt : Fin.last s < i) : b i=0 :=
    False.elim ((not_lt_of_ge (Fin.le_last i)) hlt)
  have cy:mirror A (Fin.last s)=0 := by change 1-nodes A _=0; rw [ct,sub_self]
  exact le_antisymm (fun v hv => marked_to_words hm ha ho he lo hj hv.1 hv.2)
    (fun v hv => ⟨back_sub_marked ho lo (by omega) hv,
    dirkBack_prior ha _ hb cy h1 h2 (j-2) hv _ (show Fin.last s ≤ Fin.last s from le_rfl)⟩)

/-- Every reverse word space after the cubic line is genuinely noninvariant
through the terminal-zero midpoint, including the final *incoming* edge. -/
theorem word_escape (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) {r:ℕ} (rl:2≤r) (rh:r≤m-2) :
    ¬(dirkBack A b r).map (diag (mirror A))≤dirkBack A b r := by
  obtain ⟨_,ct,col,_⟩:=last_physical hm ha ho he
  have eq (j:ℕ) (lo:2≤j) (hi:j≤m) :=zeroMarked_eq_words hm ha ho he lo hi
  have ranks (j:ℕ) (lo:2≤j) (hi:j≤m) :
      finrank K (ReverseHermite.zeroMarked A (2*m) (Fin.last s) j)=j-2 := by
    rw [eq j lo hi,word_rank hm ha ho he (by omega)]
  by_cases h:r=m-2
  · have non:=ReverseHermite.terminal_escape_in ha ho (j:=m-1) (by omega) (by omega)
      (Fin.last s) ct col (by rw [ranks _ (by omega) (by omega),ranks _ (by omega) (by omega)]; omega)
    rw [eq _ (by omega) (by omega),show m-1+1-2=r by omega] at non
    exact non
  · have non:=ReverseHermite.terminal_escape_out ha ho (j:=r+2) (by omega) (by omega)
      (Fin.last s) ct col (by rw [ranks _ (by omega) (by omega),ranks _ (by omega) (by omega)]; omega)
    rw [eq (r+2) (by omega) (by omega)] at non
    simpa using non

theorem word_one (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) : dirkBack A b 1=K ∙ tau A b := by
  obtain ⟨h1,h2⟩:=even_zero_reverse_seeds hm ha ho he
  simp [dirkBack,twoOrbit,h1,h2,tau]

/-- Only the genuinely local cubic alternative is excluded by the premise.
The whole nonlocal single-head chart and independence at the final unpaid
power follow from original arrays and paid rank comparisons. -/
theorem nonlocal_words (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) (non:¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1)
    {r:ℕ} (rl:1≤r) (rh:r≤m-2) :
    dirkBack A b r=chain (diag (mirror A)) ⊥ (tau A b) r := by
  induction r,rl using Nat.le_induction with
  | base => simpa [chain] using word_one hm ha ho he
  | succ r h ih =>
    have out:¬(dirkBack A b r).map (diag (mirror A))≤dirkBack A b r := by
      by_cases hr:r=1
      · simpa [hr] using non
      · exact word_escape hm ha ho he (by omega) (by omega)
    have below:dirkBack A b r≤dirkBack A b (r+1) := twoOrbit_le_succ .. 
    have mapped:(dirkBack A b r).map (diag (mirror A))≤dirkBack A b (r+1) :=
      le_sup_right.trans le_sup_left
    have strict:dirkBack A b r < dirkBack A b r ⊔ (dirkBack A b r).map (diag (mirror A)) :=
      lt_of_le_of_ne le_sup_left (fun e=>out (le_sup_right.trans (le_of_eq e.symm)))
    have hlt:=Submodule.finrank_lt_finrank_of_lt strict
    have r0:=word_rank hm ha ho he (r:=r) (by omega)
    have r1:=word_rank hm ha ho he (r:=r+1) (by omega)
    have exactStep:dirkBack A b (r+1)=
        dirkBack A b r ⊔ (dirkBack A b r).map (diag (mirror A)) :=
      (Submodule.eq_of_le_of_finrank_le (sup_le below mapped) (by omega)).symm
    rw [exactStep,ih (by omega),chain_sup_map (by simp) (by omega)]

theorem nonlocal_sites (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) (non:¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1) :
    m-1≤(Clock.headSites (mirror A) (tau A b)).card := by
  let n:=m-2
  have hn:0<n := by dsimp [n];omega
  have eq:=nonlocal_words hm ha ho he non (r:=n) hn (by omega)
  have out:=word_escape hm ha ho he (r:=n) (by dsimp [n]; omega) (by omega)
  rw [eq] at out
  have pay:∀k<n, (diag (mirror A)^k) (tau A b)∈chain (diag (mirror A)) ⊥ (tau A b) n :=
    ((chain_le_iff (T:=diag (mirror A)) (U:=⊥) (w:=tau A b) n).mp le_rfl).2
  have last:(diag (mirror A)^n) (tau A b)∉chain (diag (mirror A)) ⊥ (tau A b) n := by
    intro hh; apply out
    have step:=chain_sup_map (T:=diag (mirror A)) (U:=⊥) (w:=tau A b) (by simp) hn
    have le:(chain (diag (mirror A)) ⊥ (tau A b) (n+1))≤chain (diag (mirror A)) ⊥ (tau A b) n := by
      apply (chain_le_iff _).mpr
      refine ⟨bot_le,fun k hk=>?_⟩
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hk) with h|rfl
      · exact pay _ h
      · exact hh
    exact le_sup_right.trans (step ▸ le)
  have ns:=Clock.more_sites_than_paid pay last
  dsimp [n] at ns
  omega

/-- Every reverse word now has a real numerical scalar polynomial factor
on the physical array, including on zero weight coordinates. -/
theorem word_polynomial (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) (non:¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1)
    {r:ℕ} (rl:1≤r) (rh:r≤m-2) {w:Vec K (s+1)} (hw:w∈dirkBack A b r) :
    ∃P:Polynomial K,P.degree<(r:ℕ) ∧ ∀i,w i=P.eval (mirror A i)*tau A b i := by
  rw [nonlocal_words hm ha ho he non rl rh] at hw
  obtain ⟨u,hu,P,hd,huP⟩:=Clock.exists_head_poly hw
  have hz:u=0 := by simpa using hu
  exact ⟨P,hd,fun i=>by simpa [hz] using huP i⟩

/-- Every actual ordinary defect yields both sides of the physical marked
pencil, not just its fixed scalar tests. -/
theorem defect_ports (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) (non:¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1)
    {j:ℕ} (lo:3≤j) (hi:j+3≤m) {v:Vec K (s+1)} (hv:v∈zeroSpace A j) :
    ∃Q L:Polynomial K,Q.degree<(j+1:ℕ) ∧ L.degree<(j-2:ℕ) ∧
      (∀i,tau A b i≠0 → v i=Q.eval (mirror A i)) ∧
      (∀i,b i*v i=L.eval (mirror A i)*tau A b i) := by
  have τmem:tau A b∈dirkBack A b 1 := by
    rw [word_one hm ha ho he]
    exact Submodule.subset_span (Set.mem_singleton _)
  have product:=word_times_tree hm ha ho he (r:=1) (k:=j) (by omega) τmem (zeroSpace_le_treeSpace A j hv)
  obtain ⟨Q,qdeg,hQ⟩:=word_polynomial hm ha ho he non (r:=1+j) (by omega) (by omega) product
  obtain ⟨L,ldeg,hL⟩:=word_polynomial hm ha ho he non (r:=j-2) (by omega) (by omega)
    (weight_times_defect hm ha ho he (by omega) (by omega) hv)
  refine ⟨Q,L,by simpa [Nat.add_comm] using qdeg,ldeg,?_,hL⟩
  intro i hτ
  apply mul_left_cancel₀ hτ
  rw [show tau A b i*Q.eval (mirror A i)=Q.eval (mirror A i)*tau A b i by ring]
  exact hQ i

/-- On an active scalar-weight coordinate missed by the true cubic reverse
defect, *every* ordinary midpoint defect vanishes. -/
theorem weighted_clean (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) (non:¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1)
    (i:Fin (s+1)) (hi:b i≠0) (hτ:tau A b i=0) :
    ∀f∈zeroSpace A m,f i=0 := by
  intro f hf
  obtain ⟨P,_,hP⟩:=word_polynomial hm ha ho he non (r:=m-2) (by omega) le_rfl
    (weight_times_defect hm ha ho he (j:=m) (by omega) le_rfl hf)
  have hz:=hP i
  change b i*f i=_ at hz
  rw [hτ,mul_zero] at hz
  exact (mul_eq_zero.mp hz).resolve_left hi

end
end RKCert.Paired.Terminal
