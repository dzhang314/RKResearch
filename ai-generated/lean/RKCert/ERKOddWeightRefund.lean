module
public import RKCert.ERKOddLocalDrop
public import RKCert.ERKOddReverseCore

@[expose] public section
/-! # Right-hand trace refunds that do not overpay the τ product -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ:Vec K 26}{r j m:ℕ}{U:Submodule K (Vec K 26)}
noncomputable section

theorem LocalLinearBand.head_multiplication_paid (B:LocalLinearBand A b r U τ)
    {f:Vec K 26}(hf:f∈zeroSpace A j)(pay:m+j≤15-r):
    τ*f∈annih (treeSpace A m):=by
  apply mem_annih.mpr
  intro v hv
  have z:=mem_annih.mp B.paid _ (treeSpace_mono A pay (treeSpace_mul hv (zeroSpace_le_treeSpace A j hf)))
  rw [row_apply] at z ⊢
  convert z using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply]
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem paid_b_times_ordinary_defect (ho:HasTreeOrderAtLeast A b 17)
    {f:Vec K 26}(hf:f∈zeroSpace A j)(pay:m+j+1≤17):
    b*f∈annih (treeSpace A m):=by
  apply mem_annih.mpr
  intro v hv
  have z:=probe_zeroSpace ho (k:=0) (by omega) (zeroSpace_mul_treeSpace ho (by omega) hf hv)
  change probe A b 0 (f*v)=0 at z
  simp only [probe,pow_zero,mul_one,row_apply,Pi.mul_apply] at z ⊢
  convert z using 1
  apply Finset.sum_congr rfl
  intro i _
  ring

set_option maxHeartbeats 2700000 in
theorem LocalLinearBand.weight_clock_refund (B:LocalLinearBand A b r U τ)
    (ho:HasTreeOrderAtLeast A b 17){w:Vec K 26}(j8:j≤8)(jr:r+1≤j)
    (k:ℕ)(powers:∀a≤k,(diag (nodes A)^a) w∈zeroSpace A j):
    ∃u∈U,∃P:K[X],(P=0∨P.natDegree+k+(r+1)≤j)∧b*w=u+weightedEval (mirror A) τ P:=by
  let y:=mirror A
  let C:=diag (nodes A)
  let L:K[X]:=1-X
  have ll:L.natDegree=1:=one_sub_X_natDegree
  have lx(i:Fin 26):L.eval (y i)=nodes A i:=by simp [L,y,mirror]
  have rr:1≤r∧r≤2:=by rcases B.short with e|e <;> omega
  have n:9-r≤(headSites y τ).card:=B.sites
  have ord:w∈zeroSpace A j:=by simpa only [pow_zero,one_apply_eq_self] using powers 0 (Nat.zero_le _)
  obtain ⟨u,uU,T,_,b0⟩:=B.weight_trace ho ord j8
  have reps(a:ℕ)(ak:a≤k):∃P:K[X],P.natDegree≤j-(r+1)∧
      weightedEval y τ P=(fun i=>L.eval (y i)^a*weightedEval y τ T i):=by
    obtain ⟨v,vU,P,pD,bP⟩:=B.weight_trace ho (powers a ak) j8
    let rhs:=weightedEval y τ (L^a*T)
    let lhs:=weightedEval y τ P
    have hv:weightedEval y (b*w) (L^a)=b*(C^a) w:=by
      ext i
      simp only [weightedEval_apply,eval_pow,lx,Pi.mul_apply,C,pow_diag_apply]
      ring
    have eqA:weightedEval y (b*w) (L^a)=v+lhs:=hv.trans bP
    have eqB:weightedEval y (b*w) (L^a)=weightedEval y u (L^a)+rhs:=by
      rw [b0]
      ext i
      simp only [weightedEval_apply,Pi.add_apply,eval_mul,rhs,eval_pow,y]
      ring
    have eqn:lhs-rhs=weightedEval y u (L^a)-v:=by
      calc
        _=(v+lhs)-v-rhs:=by abel
        _=(weightedEval y u (L^a)+rhs)-v-rhs:=by rw [←eqA,eqB]
        _=_:=by abel
    have wu:weightedEval y u (L^a)∈U:=by
      have e:weightedEval y u (L^a)=(fun i=>(L^a).eval (y i)*u i):=by ext i;exact weightedEval_apply _ _ _ _
      rw [e];exact Clock.poly_preserves B.clock _ u uU
    have u_diff:lhs-rhs∈U:=eqn.symm ▸ U.sub_mem wu vU
    have o_diff:lhs-rhs∈annih U:=(annih U).sub_mem
      (weightedEval_orthogonal B.clock B.orthogonal _) (weightedEval_orthogonal B.clock B.orthogonal _)
    have eqP:lhs=rhs:=sub_eq_zero.mp (dot_orthogonal_inter_zero u_diff o_diff)
    refine ⟨P,?_,?_⟩
    · rcases pD with e|e
      · simp [e]
      · omega
    change lhs=_
    rw [eqP]
    ext i
    simp only [rhs,weightedEval_apply,eval_mul,eval_pow]
    ring
  obtain ⟨P,p,e⟩:=trace_degree_from_affine_shifts (c:=y) (d:=τ) L ll (h:=j-(r+1))
    (k:=k) (by omega) reps
  refine ⟨u,uU,P,?_,?_⟩
  · rcases p with z|p
    · exact Or.inl z
    · exact Or.inr (by omega)
  · change weightedEval y τ P=weightedEval y τ T at e
    rw [e]
    exact b0
end
end RKCert.Paired.ReverseHull

