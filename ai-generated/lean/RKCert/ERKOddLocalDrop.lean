module
public import RKCert.ERKOddLocalEigen

@[expose] public section
/-! # Same-grade clock refunds in the actual localized quotient -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ:Vec K 26}{r j:ℕ}{U:Submodule K (Vec K 26)}
noncomputable section

set_option maxHeartbeats 3600000 in
theorem LocalLinearBand.same_grade_refund (B:LocalLinearBand A b r U τ)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)
    (j5:5≤j)(pay:j+r+1≤8){w:Vec K 26}
    (powers:∀a≤j-4,(diag (nodes A)^a) w∈zeroSpace A j⊔reverseHidden b τ U):
    w∈reverseHidden b τ U:=by
  let y:=mirror A
  let C:=diag (nodes A)
  let K₀:=reverseHidden b τ U
  let L:K[X]:=1-X
  have ll:L.natDegree=1:=one_sub_X_natDegree
  have lx(i:Fin 26):L.eval (y i)=nodes A i:=by simp [L,y,mirror]
  have rr:1≤r∧r≤2:=by rcases B.short with e|e <;> omega
  have count:9-r≤(headSites y τ).card:=B.sites
  have split(a:ℕ)(ap:a≤j-4):∃f∈zeroSpace A j,∃z∈K₀,(C^a) w=f+z:=by
    obtain ⟨f,hf,z,hz,eq⟩:=Submodule.mem_sup.mp (powers a ap)
    exact ⟨f,hf,z,hz,eq.symm⟩
  obtain ⟨f₀,hf₀,z₀,hz₀,eq₀⟩:=split 0 (by omega)
  rw [pow_zero,one_apply_eq_self] at eq₀
  obtain ⟨u₀,hu₀,T,dT,BT⟩:=B.weight_trace ho hf₀ (by omega)
  let u:=u₀+b*z₀
  have uU:u∈U:=U.add_mem hu₀ (mem_reverseHidden.mp hz₀).2.1
  have bs:b*w=u+weightedEval y τ T:=by rw [eq₀,mul_add,BT];dsimp only [u];abel
  have pre:∀v∈U,w*v∈U:=by
    intro v vU
    rw [eq₀,add_mul]
    exact U.add_mem (B.mul_base ho (by omega) hf₀ vU) ((mem_reverseHidden.mp hz₀).2.2 _ vU)
  have qsteps(a:ℕ)(ap:a≤j-4):∃Q:K[X],Q.natDegree≤j ∧
      weightedEval y τ Q=(fun i=>L.eval (y i)^a*(τ i*w i)):=by
    obtain ⟨f,hf,z,hz,eq⟩:=split a ap
    obtain ⟨Q,dQ,fit⟩:=B.head_trace ho hf pay
    refine ⟨Q,dQ,?_⟩
    rw [fit]
    ext i
    have h:=congrFun eq i
    rw [pow_diag_apply,Pi.add_apply] at h
    have z0:=congrFun (mem_reverseHidden.mp hz).1 i
    simp only [Pi.mul_apply,Pi.zero_apply] at z0
    change τ i*f i=L.eval (y i)^a*(τ i*w i)
    rw [lx]
    linear_combination -(τ i)*h-z0
  have psteps(a:ℕ)(ap:a≤j-4):∃P:K[X],P.natDegree≤j-(r+1) ∧
      weightedEval y τ P=(fun i=>L.eval (y i)^a*weightedEval y τ T i):=by
    obtain ⟨f,hf,z,hz,eq⟩:=split a ap
    obtain ⟨v,hv,P,pd,fit⟩:=B.weight_trace ho hf (by omega)
    let aU:=v+b*z
    have au:aU∈U:=U.add_mem hv (mem_reverseHidden.mp hz).2.1
    let rhs:=weightedEval y τ (L^a*T)
    let lhs:=weightedEval y τ P
    have eqA:weightedEval y (b*w) (L^a)=aU+lhs:=by
      have ee:weightedEval y (b*w) (L^a)=b*(C^a) w:=by
        ext i
        simp only [weightedEval_apply,eval_pow,lx,Pi.mul_apply,C,pow_diag_apply]
        ring
      rw [ee,eq,mul_add,fit]
      dsimp only [aU,lhs]
      abel
    have eqB:weightedEval y (b*w) (L^a)=weightedEval y u (L^a)+rhs:=by
      rw [bs]
      ext i
      simp only [weightedEval_apply,Pi.add_apply,eval_mul,rhs,eval_pow]
      ring
    have eqn:lhs-rhs=weightedEval y u (L^a)-aU:=by
      calc
        _=(aU+lhs)-aU-rhs:=by abel
        _=(weightedEval y u (L^a)+rhs)-aU-rhs:=by rw [←eqA,eqB]
        _=_:=by abel
    have wu:weightedEval y u (L^a)∈U:=by
      have e:weightedEval y u (L^a)=(fun i=>(L^a).eval (y i)*u i):=by ext i;exact weightedEval_apply _ _ _ _
      rw [e];exact Clock.poly_preserves B.clock _ u uU
    have u_diff:lhs-rhs∈U:=eqn.symm ▸ U.sub_mem wu au
    have o_diff:lhs-rhs∈annih U:=(annih U).sub_mem
      (weightedEval_orthogonal B.clock B.orthogonal _) (weightedEval_orthogonal B.clock B.orthogonal _)
    have eqP:lhs=rhs:=sub_eq_zero.mp (dot_orthogonal_inter_zero u_diff o_diff)
    refine ⟨P,?_,?_⟩
    · rcases pd with e|e
      · simp [e]
      · omega
    change lhs=_
    rw [eqP]
    ext i
    simp only [rhs,weightedEval_apply,eval_mul,eval_pow]
    ring
  obtain ⟨Q,gQ,eQ⟩:=trace_degree_from_affine_shifts (c:=y) (d:=τ) L ll
    (h:=j) (k:=j-4) (by omega) (v:=fun i=>τ i*w i) qsteps
  obtain ⟨P,gP,eP⟩:=trace_degree_from_affine_shifts (c:=y) (d:=τ) L ll
    (h:=j-(r+1)) (k:=j-4) (by omega) psteps
  have q4:Q.natDegree≤4:=by
    rcases gQ with z|e
    · simp [z]
    · omega
  have p4:P=0∨P.natDegree+(r+1)≤4:=by
    rcases gP with z|e
    · exact Or.inl z
    · exact Or.inr (by omega)
  have qe:weightedEval (mirror A) τ Q=τ*w:=eQ
  have eqb:b*w=u+weightedEval (mirror A) τ P:=by
    change weightedEval y τ P=weightedEval y τ T at eP
    rw [eP]
    exact bs
  have Qz:=B.low_profile_zero ha ho Q P q4 p4 uU pre qe eqb
  have tz:τ*w=0:=by rw [←qe,Qz,map_zero]
  have fz:τ*f₀=0:=by
    rw [eq₀,mul_add,(mem_reverseHidden.mp hz₀).1,add_zero] at tz
    exact tz
  rw [eq₀]
  exact K₀.add_mem (B.hidden_of_zero_profile ho (by omega) hf₀ fz) hz₀
end
end RKCert.Paired.ReverseHull

