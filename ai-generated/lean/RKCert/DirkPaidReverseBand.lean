module
public import RKCert.DirkReverseHermite
public import RKCert.DirkReversePivot
public import RKCert.DirkEvenReverseProfile
@[expose] public section
namespace RKCert.Paired.Terminal
open Module RKCert.OneEscape
variable {K:Type*} [Field K] [CharZero K] {s p H:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
noncomputable section

/-- Native evidence sufficient for the local/nonlocal reverse cubic
dichotomy, including a terminal-deleted marked horizon. Clearing one
coordinate of a true marked row is not an RK stage deletion. -/
structure PaidReverseBand (A:Fin (s+1)→Fin (s+1)→K) (b:Vec K (s+1)) (p H:ℕ):Prop where
  low:7≤H
  paid:2*H≤p
  terminal:nodes A (Fin.last s)=1
  col:∀i,A i (Fin.last s)=0
  seeds:backSeed1 A b=0 ∧ q₂ (transMat A) (mirror A) b=0
  rank:∀ {r:ℕ},r+2≤H→finrank K (dirkBack A b r)=r
  cover:∀j,2≤j→j≤H→ReverseHermite.zeroMarked A p (Fin.last s) j=dirkBack A b (j-2)

namespace PaidReverseBand
omit [CharZero K] in
theorem one (D:PaidReverseBand A b p H):dirkBack A b 1=K ∙ tau A b:=by
  obtain ⟨d1,d2⟩:=D.seeds
  simp [dirkBack,twoOrbit,d1,d2,tau]
omit [CharZero K] in
theorem to_words (D:PaidReverseBand A b p H) {j:ℕ} (l:2≤j) (h:j≤H) {w:Vec K (s+1)}
    (hw:w∈marked A p j) (last:w (Fin.last s)=0):w∈dirkBack A b (j-2):=
    D.cover j l h ▸ (show w∈ReverseHermite.zeroMarked A p (Fin.last s) j from ⟨hw,last⟩)

theorem escape (D:PaidReverseBand A b p H) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    {r:ℕ} (rl:2≤r) (rh:r+2≤H):¬(dirkBack A b r).map (diag (mirror A))≤dirkBack A b r:=by
  have hi:=D.paid;have low:=D.low
  have sizes(j:ℕ) (a:2≤j) (c:j≤H):finrank K (ReverseHermite.zeroMarked A p (Fin.last s) j)=j-2:=by
    rw [D.cover j a c,D.rank (by omega)]
  by_cases top:r+2=H
  · have out:=ReverseHermite.terminal_escape_in ha ho (j:=H-1) (by omega) (by omega)
      (Fin.last s) D.terminal D.col (by rw [sizes _ (by omega) (by omega),sizes _ (by omega) (by omega)];omega)
    rw [D.cover _ (by omega) (by omega),show H-1+1-2=r by omega] at out
    exact out
  · have out:=ReverseHermite.terminal_escape_out ha ho (j:=r+2) (by omega) (by omega)
      (Fin.last s) D.terminal D.col (by rw [sizes _ (by omega) (by omega),sizes _ (by omega) (by omega)];omega)
    rw [D.cover _ (by omega) (by omega)] at out
    simpa using out

theorem nonlocal_words (D:PaidReverseBand A b p H) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (non:¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1)
    {r:ℕ} (rl:1≤r) (rh:r≤H-2) :
    dirkBack A b r=chain (diag (mirror A)) ⊥ (tau A b) r := by
  have hm:=D.low;have hp:=D.paid
  induction r,rl using Nat.le_induction with
  | base => simpa [chain] using D.one
  | succ r h ih =>
    have out:¬(dirkBack A b r).map (diag (mirror A))≤dirkBack A b r := by
      by_cases hr:r=1
      · simpa [hr] using non
      · exact D.escape ha ho (by omega) (by omega)
    have below:dirkBack A b r≤dirkBack A b (r+1) := twoOrbit_le_succ .. 
    have mapped:(dirkBack A b r).map (diag (mirror A))≤dirkBack A b (r+1) :=
      le_sup_right.trans le_sup_left
    have strict:dirkBack A b r < dirkBack A b r ⊔ (dirkBack A b r).map (diag (mirror A)) :=
      lt_of_le_of_ne le_sup_left (fun e=>out (le_sup_right.trans (le_of_eq e.symm)))
    have hlt:=Submodule.finrank_lt_finrank_of_lt strict
    have r0:=D.rank (r:=r) (by omega)
    have r1:=D.rank (r:=r+1) (by omega)
    have exactStep:dirkBack A b (r+1)=
        dirkBack A b r ⊔ (dirkBack A b r).map (diag (mirror A)) :=
      (Submodule.eq_of_le_of_finrank_le (sup_le below mapped) (by omega)).symm
    rw [exactStep,ih (by omega),chain_sup_map (by simp) (by omega)]

theorem nonlocal_sites (D:PaidReverseBand A b p H) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (non:¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1) :
    H-1≤(Clock.headSites (mirror A) (tau A b)).card := by
  have hm:=D.low;have hp:=D.paid
  let n:=H-2
  have hn:0<n := by dsimp [n];omega
  have eq:=D.nonlocal_words ha ho non (r:=n) hn (by omega)
  have out:=D.escape ha ho (r:=n) (by dsimp [n]; omega) (by omega)
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
theorem word_polynomial (D:PaidReverseBand A b p H) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (non:¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1)
    {r:ℕ} (rl:1≤r) (rh:r≤H-2) {w:Vec K (s+1)} (hw:w∈dirkBack A b r) :
    ∃P:Polynomial K,P.degree<(r:ℕ) ∧ ∀i,w i=P.eval (mirror A i)*tau A b i := by
  have hm:=D.low;have hp:=D.paid
  rw [D.nonlocal_words ha ho non rl rh] at hw
  obtain ⟨u,hu,P,hd,huP⟩:=Clock.exists_head_poly hw
  have hz:u=0 := by simpa using hu
  exact ⟨P,hd,fun i=>by simpa [hz] using huP i⟩

theorem local_words (D:PaidReverseBand A b p H) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (localc:(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1) :
    ∃w:Vec K (s+1), w∈dirkBack A b 2 ∧
      ∀r:ℕ,1≤r → r≤H-2 →
      dirkBack A b r=chain (diag (mirror A)) (dirkBack A b 1) w (r-1) := by
  have hm:=D.low;have hp:=D.paid
  classical
  have r1:=D.rank (r:=1) (by omega)
  have r2:=D.rank (r:=2) (by omega)
  have ex:∃w:Vec K (s+1), w∈dirkBack A b 2 ∧ w∉dirkBack A b 1 := by
    by_contra! hn
    have inc:dirkBack A b 2≤dirkBack A b 1 := hn
    have dim:=Submodule.finrank_mono inc; omega
  obtain ⟨w,hw,hnot⟩:=ex
  have base:dirkBack A b 2=chain (diag (mirror A)) (dirkBack A b 1) w 1 := by
    simp only [chain,pow_zero,Module.End.one_eq_id,LinearMap.id_apply]
    have hle:dirkBack A b 1≤dirkBack A b 2 := twoOrbit_le_succ ..
    exact (Submodule.eq_of_le_of_finrank_le (sup_le hle ((Submodule.span_singleton_le_iff_mem ..).mpr hw))
      (by rw [Submodule.finrank_sup_span_singleton hnot,r1,r2])).symm
  refine ⟨w,hw,fun r hr rh=>?_⟩
  induction r,hr using Nat.le_induction with
  | base => rfl
  | succ r hc ih =>
    by_cases e:r=1
    · simpa [e] using base
    have out:=D.escape ha ho (r:=r) (by omega) (by omega)
    have below:dirkBack A b r≤dirkBack A b (r+1) := twoOrbit_le_succ ..
    have mapped:(dirkBack A b r).map (diag (mirror A))≤dirkBack A b (r+1) :=
      le_sup_right.trans le_sup_left
    have lt:dirkBack A b r < dirkBack A b r ⊔ (dirkBack A b r).map (diag (mirror A)) :=
      lt_of_le_of_ne le_sup_left (fun h=>out (le_sup_right.trans (le_of_eq h.symm)))
    have hlt:=Submodule.finrank_lt_finrank_of_lt lt
    have now:=D.rank (r:=r) (by omega)
    have later:=D.rank (r:=r+1) (by omega)
    have inc:dirkBack A b (r+1)=dirkBack A b r ⊔ (dirkBack A b r).map (diag (mirror A)) :=
      (Submodule.eq_of_le_of_finrank_le (sup_le below mapped) (by omega)).symm
    rw [inc,ih (by omega),chain_sup_map localc (by omega),show r-1+1=r+1-1 by omega]

omit [CharZero K] in
/-- The active part of the local cubic is supported on *one numerical
reflected abscissa*, which may contain many signed/duplicated rows. -/
theorem local_pivot (D:PaidReverseBand A b p H) (_ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (localc:(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1) :
    ∃h:Fin (s+1), tau A b h≠0 ∧ (∀j,h < j → tau A b j=0) ∧
    (∀i,tau A b i≠0 → mirror A i=mirror A h) ∧ row (tau A b) 1=0 := by
  have hm:=D.low;have hp:=D.paid
  have lone:=D.one
  have r1:=D.rank (r:=1) (by omega)
  have nz:tau A b≠0 := by
    intro eqn
    have bot:dirkBack A b 1=⊥:=lone.trans (Submodule.span_singleton_eq_bot.mpr eqn)
    rw [bot] at r1
    simp at r1
  obtain ⟨h,dh,pre⟩:=exists_last_coordinate nz
  have hd:tau A b∈dirkBack A b 1 := by rw [lone];exact Submodule.subset_span (Set.mem_singleton _)
  have heig:=localc (Submodule.mem_map_of_mem hd : diag (mirror A) (tau A b) ∈ (dirkBack A b 1).map (diag (mirror A)))
  rw [lone] at heig
  obtain ⟨lam,hlam⟩:=Submodule.mem_span_singleton.mp heig
  have ev (i:Fin (s+1)) (di:tau A b i≠0) : lam=mirror A i := by
    have eqn:=congrFun hlam i
    change lam*tau A b i=mirror A i*tau A b i at eqn
    exact mul_right_cancel₀ di eqn
  have hm3:tau A b∈marked A (p) 3 := seed3_marked ho (by omega)
  exact ⟨h,dh,pre,fun i hi => (ev i hi).symm.trans (ev h dh),leaf_marked_zero hm3⟩

end PaidReverseBand
end
end RKCert.Paired.Terminal
