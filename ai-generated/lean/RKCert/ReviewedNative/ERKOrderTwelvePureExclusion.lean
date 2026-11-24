module

public import RKCert.ReviewedNative.ERKOrderTwelveRankTwoFour
public import RKCert.OrderTwelveDivisors

public section

/-! # The pure width-seventeen chart is impossible at strict order twelve

The first actual off-core, off-head mismatch extracts a paid primitive
zero. The exact terminal factorization routes it to the checked
tree-free divisor gate, with no assumption about root splitting.
-/
namespace RKResearch.Certified.Graded.ERK12

open RKResearch Polynomial Module Reverse RKCert.OneEscape RKCert.Endpoint
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

/-- Any linear contrast against a paid pure quartic produces a true
off-core and off-head row with nonzero polynomial value and zero
primitive. Both the core mask and the row remain physical. -/
theorem pure_profile_primitive_zero (ha : ∀ i k, i≤k → A i k=0)
    (ho : HasOrder 12 A b) {U : Submodule K (Fin (s+1) → K)}
    {z : Fin (s+1) → K} {α : K} {Q R : K[X]}
    (H : RankTwoFourProfile A U z α Q R) (r0 : R≠0)
    (head : ∀ i, z i≠0 → z i=R.eval (nodes A i))
    {M : K[X]} (m0 : M≠0) (md : M.natDegree≤1) :
    ∃ k : Fin (s+1), ¬LiveCore.live U k ∧ z k=0 ∧
      (M*R).eval (nodes A k)≠0 ∧ (primitive (M*R)).eval (nodes A k)=0 := by
  classical
  obtain ⟨e,he,live⟩ := LiveCore.exists_live_indicator U H.closed
  let c := nodes A
  let F := M*R
  let feed := weightedEval c z M+weightedEval c e F
  let d := evalNodes A F-feed
  have degF : F.natDegree≤5 := natDegree_mul_le.trans (Nat.add_le_add md H.rDegree)
  have eF : weightedEval c e F∈U := by
    have h : weightedEval c e F=fun i => F.eval (c i)*e i := by ext i; simp
    rw [h]
    exact clock_function_mem (fun u hu => H.stable (Submodule.mem_map_of_mem hu)) F.eval he
  have feed5 : feed∈zeroSpace A 5 := (zeroSpace A 5).add_mem
    (weighted_clock_mem_grade ho H.headInFour (n:=1) (by decide) M md)
    (zeroSpace_mono A (by decide : 4≤5) (H.coreInside eF))
  have dn : d≠0 := by
    intro de
    have fit : evalNodes A F=feed := sub_eq_zero.mp de
    have sep : PolySeparated A 5 := PolySeparated.of_coeff
      (explicit_coeff_separated ha ho (q:=5) (by decide))
    exact (mul_ne_zero m0 r0) (sep F degF (fit.symm ▸ feed5))
  have witness : ∃ i, d i≠0 := by
    by_contra! h
    exact dn (funext h)
  obtain ⟨k,kn,before⟩ := Reverse.TwoNode.earliest (Equiv.refl _) (fun i => d i≠0) witness
  have dk (i : Fin (s+1)) : d i=F.eval (c i)-(M.eval (c i)*z i+F.eval (c i)*e i) := by
    simp only [d,feed,Pi.sub_apply,Pi.add_apply,evalNodes_apply,weightedEval_apply,c]
  have off : ¬LiveCore.live U k := by
    intro h
    apply kn
    rw [dk,H.disjoint k h,live k,ite_eq_left h,mul_zero,mul_one,zero_add,sub_self]
  have zero : z k=0 := by
    by_contra hn
    apply kn
    rw [dk,head k hn,live k,ite_eq_right off,mul_zero,add_zero]
    simp only [F,c,eval_mul,sub_self]
  have val : d k=F.eval (c k) := by
    rw [dk,zero,live k,ite_eq_right off,mul_zero,mul_zero,add_zero,sub_zero]
  have caus : mat A d k=0 := causal_mat ha k d (fun i hi => not_not.mp (before i hi))
  let Y := evalNodes A (primitive F)-mat A d
  have pay : Y∈zeroSpace A 6 := by
    have e : Y=-(mat A (evalNodes A F)-evalNodes A (primitive F))+mat A feed := by
      dsimp only [Y,d]
      rw [map_sub]
      abel
    rw [e]
    exact (zeroSpace A 6).add_mem ((zeroSpace A 6).neg_mem (primitive_defect A F degF))
      (mat_zeroSpace_charZero A 5 feed5)
  obtain ⟨u,hu,L,_,eq⟩ := HeadFiber.exists_poly (H.sixth ▸ pay)
  have p : (primitive F).eval (c k)=0 := by
    have e := congrFun eq k
    simpa only [Y,Pi.sub_apply,evalNodes_apply,c,caus,sub_zero,Pi.add_apply,
      LiveCore.val_eq_zero_of_not_live off hu,weightedEval_apply,zero,mul_zero,zero_add] using e
  exact ⟨k,off,zero,by rwa [←val],p⟩

theorem terminalMesh6_eq_X_dFivePoly :
    (terminalMesh6 : K[X])=X*RKCert.OrderTwelve.dFivePoly := by
  let _ : Infinite K := Infinite.of_injective (fun n : ℕ => (n:K)) Nat.cast_injective
  apply Polynomial.funext
  intro x
  rw [terminalMesh6_value,eval_mul,eval_X,RKCert.OrderTwelve.eval_dFivePoly]
  rfl

private theorem primitive_divisor_formula (P : K[X]) (d : P.natDegree≤4) (x : K) :
    (primitive (X*P)).eval x=RKCert.OrderTwelve.purePolynomialMoment P x := by
  classical
  let a : Fin 5 → K := fun i => P.coeff i.val
  have rep : ofFn 5 a=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  have e := HeadContrast.primitive_monomial_moment a x 1
  rw [pow_one,rep] at e
  rw [e]
  unfold RKCert.OrderTwelve.purePolynomialMoment RKCert.OrderTwelve.pureMoment
  norm_num [RKCert.ReviewedNative.TwoKnot.moment,Fin.sum_univ_succ,a]
  ring

/-- If the remaining physical profile has zero leakage, the two-factor
mesh split contradicts the exact Appendix B scalar divisor certificate. -/
theorem exclude_pure_rank_two_four (ha : ∀ i k, i≤k → A i k=0)
    (ho : HasOrder 12 A b) (S : Saturation A b)
    {U : Submodule K (Fin (s+1) → K)} {z : Fin (s+1) → K}
    {α : K} {Q R : K[X]} (H : RankTwoFourProfile A U z α Q R) (pure : α=0) : False := by
  classical
  obtain ⟨mesh,dr,dq,head⟩ := H.pure_factor pure
  have r0 : R≠0 := by intro r; simp [r] at dr
  let D : K[X] := RKCert.OrderTwelve.dFivePoly
  have fact : X*D=R*Q := terminalMesh6_eq_X_dFivePoly.symm.trans mesh
  have contradict (M P : K[X]) (mn : M≠0) (dm : M.natDegree≤1)
      (dp : P.natDegree=3 ∨ P.natDegree=4) (div : P∣D) (fit : M*R=X*P) : False := by
    obtain ⟨k,off,zero,kn,kp⟩ := pure_profile_primitive_zero ha ho H r0 head mn dm
    rw [fit] at kn kp
    have nd : nodes A k≠0 ∧ P.eval (nodes A k)≠0 := by
      rw [eval_mul,eval_X] at kn
      exact mul_ne_zero_iff.mp kn
    have eligible : nodes A k=1 ∨
        RKCert.OrderTwelve.dFive (nodes A k)=0 ∧ P.eval (nodes A k)≠0 := by
      by_cases last : k=Fin.last s
      · exact Or.inl (last.symm ▸ S.terminalClock)
      right
      have coord : coordinate (K:=K) (Fin.last s) k=0 := by simp [coordinate,last]
      have h := H.mesh k off
      rw [coord,zero,zero_mul,add_zero,terminalMesh6_eq_X_dFivePoly,eval_mul,eval_X,
        RKCert.OrderTwelve.eval_dFivePoly] at h
      exact ⟨(mul_eq_zero.mp h).resolve_left nd.1,nd.2⟩
    have n := RKCert.OrderTwelve.pure_divisor_moment_ne_zero P div (nodes A k) dp eligible
    exact n ((primitive_divisor_formula P (by omega) (nodes A k)) ▸ kp)
  by_cases hR : R.eval 0=0
  · let P := R.divX
    have c0 : R.coeff 0=0 := by rwa [coeff_zero_eq_eval_zero]
    have eq : X*P=R := by simpa [P,c0] using X_mul_divX_add R
    have p0 : P≠0 := by intro no; apply r0; rw [←eq,no,mul_zero]
    have d := natDegree_X_mul p0
    rw [eq,dr] at d
    have div : D=P*Q := by
      apply mul_left_cancel₀ X_ne_zero
      rw [←mul_assoc,eq]
      exact fact
    exact contradict 1 P one_ne_zero (by simp) (Or.inl (by omega)) ⟨Q,div⟩ (by rw [one_mul,eq])
  · have ep := congrArg (Polynomial.eval (0:K)) fact
    rw [eval_mul,eval_X,zero_mul,eval_mul] at ep
    have c0 : Q.coeff 0=0 := by
      rw [coeff_zero_eq_eval_zero]
      exact (mul_eq_zero.mp ep.symm).resolve_left hR
    have eq : X*Q.divX=Q := by simpa [c0] using X_mul_divX_add Q
    have div : D=R*Q.divX := by
      apply mul_left_cancel₀ X_ne_zero
      calc
        X*D = R*Q := fact
        _ = R*(X*Q.divX) := congrArg (fun P => R*P) eq.symm
        _ = X*(R*Q.divX) := by ring
    exact contradict X R X_ne_zero (by simp) (Or.inr dr) ⟨Q.divX,div⟩ rfl

/-- A width-seventeen strict order-twelve tableau can only have the
genuine nonzero-leak physical profile. -/
theorem actual_nonzero_leak_profile_at_cap (ha : ∀ i k, i≤k → A i k=0)
    (ho : HasOrder 12 A b) (cap : s+1≤17) :
    ∃ U z α Q R, RankTwoFourProfile A U z α Q R ∧ α≠0 := by
  have S := saturation_of_order ha ho cap
  obtain ⟨U,z,α,Q,R,H,_⟩ := actual_rank_two_four_profile ha ho cap
  exact ⟨U,z,α,Q,R,H,fun h => exclude_pure_rank_two_four ha ho S H h⟩

end RKResearch.Certified.Graded.ERK12

