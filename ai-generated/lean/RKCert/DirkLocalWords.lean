module
public import RKCert.DirkReversePivot
@[expose] public section
namespace RKCert.Paired.Terminal
open Module RKCert.OneEscape
variable {K : Type*} [Field K] [CharZero K] {s m:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
noncomputable section

/-- Rank-saturated local cubic chart, with no multiplication of adjoint
rows. The cubic line is the only exceptional direction in grades 4–m. -/
theorem local_words (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) (localc:(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1) :
    ∃w:Vec K (s+1), w∈dirkBack A b 2 ∧
      ∀r:ℕ,1≤r → r≤m-2 →
      dirkBack A b r=chain (diag (mirror A)) (dirkBack A b 1) w (r-1) := by
  classical
  have r1:=word_rank hm ha ho he (r:=1) (by omega)
  have r2:=word_rank hm ha ho he (r:=2) (by omega)
  have ex:∃w:Vec K (s+1), w∈dirkBack A b 2 ∧ w∉dirkBack A b 1 := by
    by_contra! hn
    have inc:dirkBack A b 2≤dirkBack A b 1 := hn
    have dim:=Submodule.finrank_mono inc; omega
  obtain ⟨w,hw,hnot⟩:=ex
  have base:dirkBack A b 2=chain (diag (mirror A)) (dirkBack A b 1) w 1 := by
    simp only [chain,pow_zero,one_apply_eq_self]
    have hle:dirkBack A b 1≤dirkBack A b 2 := twoOrbit_le_succ ..
    exact (Submodule.eq_of_le_of_finrank_le (sup_le hle ((Submodule.span_singleton_le_iff_mem ..).mpr hw))
      (by rw [Submodule.finrank_sup_span_singleton hnot,r1,r2])).symm
  refine ⟨w,hw,fun r hr rh=>?_⟩
  induction r,hr using Nat.le_induction with
  | base => rfl
  | succ r hc ih =>
    by_cases e:r=1
    · simpa [e] using base
    have out:=word_escape hm ha ho he (r:=r) (by omega) (by omega)
    have below:dirkBack A b r≤dirkBack A b (r+1) := twoOrbit_le_succ ..
    have mapped:(dirkBack A b r).map (diag (mirror A))≤dirkBack A b (r+1) :=
      le_sup_right.trans le_sup_left
    have lt:dirkBack A b r < dirkBack A b r ⊔ (dirkBack A b r).map (diag (mirror A)) :=
      lt_of_le_of_ne le_sup_left (fun h=>out (le_sup_right.trans (le_of_eq h.symm)))
    have hlt:=Submodule.finrank_lt_finrank_of_lt lt
    have now:=word_rank hm ha ho he (r:=r) (by omega)
    have later:=word_rank hm ha ho he (r:=r+1) (by omega)
    have inc:dirkBack A b (r+1)=dirkBack A b r ⊔ (dirkBack A b r).map (diag (mirror A)) :=
      (Submodule.eq_of_le_of_finrank_le (sup_le below mapped) (by omega)).symm
    rw [inc,ih (by omega),chain_sup_map localc (by omega),show r-1+1=r+1-1 by omega]

/-- The active part of the local cubic is supported on *one numerical
reflected abscissa*, which may contain many signed/duplicated rows. -/
theorem local_pivot (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) (localc:(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1) :
    ∃h:Fin (s+1), tau A b h≠0 ∧ (∀j,h < j → tau A b j=0) ∧
    (∀i,tau A b i≠0 → mirror A i=mirror A h) ∧ row (tau A b) 1=0 := by
  have lone:=word_one hm ha ho he
  have r1:=word_rank hm ha ho he (r:=1) (by omega)
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
  have hm3:tau A b∈marked A (2*m) 3 := seed3_marked ho (by omega)
  exact ⟨h,dh,pre,fun i hi => (ev i hi).symm.trans (ev h dh),leaf_marked_zero hm3⟩

end
end RKCert.Paired.Terminal
