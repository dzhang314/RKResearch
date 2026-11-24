module
public import RKCert.ERKOddFourAxis
public import RKCert.ERKOddLocalHeadTrace

@[expose] public section
/-! # The only three real grade-nine advances in the exceptional order-17 band
Every promoted vector is an element of the true annihilator of E7.
There is no rank equality assertion for a new backward flag. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ h ξ W:Vec K 26}{U:Submodule K (Vec K 26)}{Q:K[X]}
noncomputable section

structure TrueLocalMode (A:Fin 26→Fin 26→K)(τ ξ ℓ:Vec K 26)(U:Submodule K (Vec K 26))(a c:K):Prop where
  nonzero:ℓ≠0
  paid:ℓ∈annih (treeSpace A 7)
  orthogonal:ℓ∈annih U
  support:∀i,mirror A i≠a→ℓ i=0
  values:∀i,mirror A i=a→ℓ i=τ i*(ξ i-c)

structure TrueRationalAdvance (A:Fin 26→Fin 26→K)(τ:Vec K 26)(a:K):Prop where
  omitted:∀i,mirror A i=a→τ i=0
  paid:(fun i=>τ i/(mirror A i-a))∈annih (treeSpace A 7)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem affine_root_factor (T:K[X])(d:T.natDegree=1):
    ∃k a:K,k≠0∧T=C k*(X-C a):=by
  let k:=T.coeff 1
  have kn:k≠0:=by
    change T.coeff 1≠0
    rw [←d,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (by intro z;rw [z,natDegree_zero] at d;omega)
  let a:=-T.coeff 0/k
  have ka:k*a= -T.coeff 0:=by dsimp only [a];field_simp [kn]
  refine ⟨k,a,kn,?_⟩
  have e:T=C (T.coeff 0)+C k*X:=by
    conv_lhs=>rw [T.as_sum_range_C_mul_X_pow' (n:=2) (by omega)]
    simp [Finset.sum_range_succ,k]
  rw [e,mul_sub,←map_mul,ka,map_neg]
  ring

private theorem weighted_polynomial_advance (B:LocalLinearBand A b 2 U τ)
    (R:K[X])(d:R.natDegree=7)
    (pay:weightedEval (mirror A) τ R∈annih (treeSpace A 7)):
    weightedEval (mirror A) τ (X^7)∈annih (treeSpace A 7):=by
  let a:=R.coeff 7
  have an:a≠0:=by
    change R.coeff 7≠0
    rw [←d,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (by intro e;rw [e,natDegree_zero] at d;omega)
  let S:=R-C a*X^7
  have sd:S.natDegree≤6:=by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    change (R-C a*X^7).coeff j=0
    rw [coeff_sub,C_mul_X_pow_eq_monomial,coeff_monomial]
    by_cases e:j=7
    · subst j;simp [a]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega:R.natDegree<j)]
      simp [e]
  have s0:=B.head_reflect_paid 7 S (by omega:7+S.natDegree≤15-2)
  have t:weightedEval (mirror A) τ (R-S)∈annih (treeSpace A 7):=by
    simpa only [map_sub] using (annih (treeSpace A 7)).sub_mem pay s0
  have e:R-S=a•((X:K[X])^7):=by dsimp only [S];rw [smul_eq_C_mul];ring
  rw [e,map_smul] at t
  simpa only [smul_smul,inv_mul_cancel₀ an,one_smul] using (annih (treeSpace A 7)).smul_mem a⁻¹ t

set_option maxHeartbeats 5100000 in
theorem LocalLinearBand.four_mask_modes (B:LocalLinearBand A b 2 U τ)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)
    (D:LocalFourAxis A b τ h ξ U)(H:LocalHeadContrast A b τ h W U Q):
    weightedEval (mirror A) τ (X^7)∈annih (treeSpace A 7) ∨
      (∃a:K,TrueRationalAdvance A τ a) ∨
      (∃a c:K,∃ℓ:Vec K 26,TrueLocalMode A τ ξ ℓ U a c):=by
  let y:=mirror A
  have ζ:τ*ξ∈annih (treeSpace A 7):=B.head_multiplication_paid D.sixth (by decide)
  have zo:τ*ξ∈annih U:=B.mul_head_orthogonal ho (by decide) D.sixth
  obtain ⟨v,vU,P,pD,bv⟩:=D.bRefund
  have keep:∀u∈U,ξ*u∈U:=fun u hu=>B.mul_base ho (by decide) D.sixth hu
  have small (R:K[X])(rd:R.natDegree≤4)(fit:weightedEval y τ R=τ*ξ):False:=by
    have q:=B.low_profile_zero ha ho R P rd (Or.inr (by omega)) vU keep fit bv
    have he:τ*ξ=0:=by rw [←fit,q,map_zero]
    exact D.axisOut (B.hidden_of_zero_profile ho (by decide) D.sixth he)
  have qfit(i:Fin 26):Q.eval (y i)*τ i=τ i*h i:=by
    by_cases n:τ i=0
    · simp [n]
    · rw [(H.headValue i n).1,mul_comm]
  rcases D.geometry with ⟨a,off⟩|⟨T,tn,td,powers,f⟩
  · right;right
    have nz:τ*ξ≠0:=fun e=>D.axisOut (B.hidden_of_zero_profile ho (by decide) D.sixth e)
    exact ⟨a,0,τ*ξ,⟨nz,ζ,zo,fun i n=>by rw [Pi.mul_apply,off i n,mul_zero],
      fun i _=>by rw [Pi.mul_apply,sub_zero]⟩⟩
  by_cases T0:T.natDegree=0
  · let k:=T.coeff 0
    have hT:T=C k:=eq_C_of_natDegree_eq_zero T0
    have kn:k≠0:=fun z=>tn (by rw [hT,z,map_zero])
    let R:=C k⁻¹*Q
    have cR:R.natDegree=Q.natDegree:=natDegree_C_mul (inv_ne_zero kn)
    have fit:weightedEval y τ R=τ*ξ:=by
      ext i
      simp only [weightedEval_apply,R,eval_mul,eval_C,Pi.mul_apply]
      apply mul_right_cancel₀ kn
      have q:=qfit i
      rw [f i,hT,eval_C] at q
      field_simp [kn]
      linear_combination q
    by_cases r4:R.natDegree≤4
    · exact False.elim (small R r4 fit)
    have rd:R.natDegree=5:=by have d:=H.degree;omega
    let L:K[X]:=1-X
    let S:=L^2*R
    have Ld:L.natDegree=1:=one_sub_X_natDegree
    have Ln:L≠0:=by intro e;rw [e,natDegree_zero] at Ld;omega
    have Rn:R≠0:=by intro e;rw [e,natDegree_zero] at rd;omega
    have sd:S.natDegree=7:=by
      dsimp only [S]
      rw [natDegree_mul (pow_ne_zero _ Ln) Rn,natDegree_pow,Ld,rd]
    have e:weightedEval y τ S=τ*((diag (nodes A)^2) ξ):=by
      ext i
      have f:=congrFun fit i
      simp only [weightedEval_apply,Pi.mul_apply] at f
      have g:L.eval (y i)=nodes A i:=by simp [y,L,mirror]
      simp only [S,weightedEval_apply,eval_mul,eval_pow,g,Pi.mul_apply,pow_diag_apply]
      rw [mul_assoc,f]
      ring
    have z:weightedEval y τ S∈annih (treeSpace A 7):=by
      rw [e]
      exact B.head_multiplication_paid (powers 2 (by decide)) (by decide)
    exact Or.inl (weighted_polynomial_advance B S sd z)
  have T1:T.natDegree=1:=by omega
  obtain ⟨k,a,kn,he⟩:=affine_root_factor T T1
  let S:=C k⁻¹*Q
  have Sd:S.natDegree≤5:=natDegree_mul_le.trans (by have h:=H.degree;rw [natDegree_C];omega)
  have aff(i:Fin 26):(y i-a)*(τ i*ξ i)=S.eval (y i)*τ i:=by
    simp only [S,eval_mul,eval_C]
    apply mul_right_cancel₀ kn
    have eq:=qfit i
    rw [f i,he] at eq
    simp only [eval_mul,eval_C,eval_sub,eval_X] at eq
    field_simp [kn]
    linear_combination -eq
  obtain ⟨R,R_eq⟩:=X_sub_C_dvd_sub_C_eval (p:=S) (a:=a)
  have Rd:R.natDegree≤4:=by
    by_cases r:R=0
    · simp [r]
    have q:=natDegree_sub_le S (C (S.eval a))
    rw [R_eq,natDegree_mul (X_sub_C_ne_zero _) r,natDegree_X_sub_C,natDegree_C] at q
    omega
  let ℓ:=τ*ξ-weightedEval y τ R
  have h7:weightedEval y τ R∈annih (treeSpace A 7):=B.head_reflect_paid 7 R (by omega)
  have paid:ℓ∈annih (treeSpace A 7):=(annih (treeSpace A 7)).sub_mem ζ h7
  have orth:ℓ∈annih U:=(annih U).sub_mem zo (weightedEval_orthogonal B.clock B.orthogonal R)
  have rel(i:Fin 26):(y i-a)*ℓ i=S.eval a*τ i:=by
    have p:=congrArg (eval (y i)) R_eq
    simp only [eval_sub,eval_mul,eval_X,eval_C] at p
    simp only [ℓ,Pi.sub_apply,Pi.mul_apply,weightedEval_apply]
    linear_combination aff i+τ i*p
  by_cases Sn:S.eval a=0
  · right;right
    have ln:ℓ≠0:=by
      intro e
      have fit:=sub_eq_zero.mp e
      exact small R Rd fit.symm
    refine ⟨a,R.eval a,ℓ,⟨ln,paid,orth,?_,?_⟩⟩
    · intro i ne
      have q:=rel i
      rw [Sn,zero_mul] at q
      exact (mul_eq_zero.mp q).resolve_left (sub_ne_zero.mpr ne)
    · intro i e
      change y i=a at e
      simp only [ℓ,Pi.sub_apply,Pi.mul_apply,weightedEval_apply,e]
      ring
  right;left
  have absent(i:Fin 26)(ei:y i=a):τ i=0:=by
    have q:=rel i
    rw [ei,sub_self,zero_mul] at q
    exact (mul_eq_zero.mp q.symm).resolve_left Sn
  let t:Vec K 26:=fun i=>τ i/(y i-a)
  have eq:ℓ=S.eval a•t:=by
    ext i
    simp only [Pi.smul_apply,smul_eq_mul,t]
    by_cases z:y i=a
    · have n:=absent i z
      simp [ℓ,n]
    field_simp [sub_ne_zero.mpr z]
    exact (mul_comm _ _).trans (rel i)
  have th:t∈annih (treeSpace A 7):=by
    rw [eq] at paid
    simpa only [smul_smul,inv_mul_cancel₀ Sn,one_smul] using
      (annih (treeSpace A 7)).smul_mem (S.eval a)⁻¹ paid
  exact ⟨a,⟨absent,th⟩⟩
end
end RKCert.Paired.ReverseHull

