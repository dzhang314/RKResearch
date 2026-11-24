module
public import RKCert.ERKOddLocalPort

@[expose] public section
/-! # Low-degree localized traces land in the genuine hidden mask algebra -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ f:Vec K 26}{r:ℕ}{U:Submodule K (Vec K 26)}
noncomputable section

private theorem localized_contrast_not_base (B:LocalLinearBand A b r U τ)
    (ho:HasTreeOrderAtLeast A b 17)(Q P H:K[X]) {u:Vec K 26}(uU:u∈U)
    (qn:Q≠0)(hn:H≠0)(dQ:Q.natDegree≤4)(dH:H.natDegree≤2)(dP:P.natDegree≤3)
    (spec:localContrast A b f Q=weightedEval (mirror A) b Q-weightedEval (mirror A) τ P-u):
    weightedEval (mirror A) (localContrast A b f Q) H∉U:=by
  intro inU
  let y:=mirror A
  let W:=localContrast A b f Q
  let R:=H^2*Q
  have rd:R.natDegree≤8:=by
    have a:=natDegree_mul_le (p:=H^2) (q:=Q)
    rw [natDegree_pow] at a
    dsimp only [R];omega
  have hh:(H*Q).natDegree≤6:=natDegree_mul_le.trans (by omega)
  have rr:r≤2:=by rcases B.short with e|e <;> omega
  have rn:=B.local_contrast_moments ho Q P R uU spec (by omega) (by omega) (by omega)
  have eq:=mem_annih.mp (B.base_annih ho inU) _ (mirror_eval_in_tree (A:=A) (H*Q) (hh.trans (by omega:6≤16-r)))
  have ev:(∑i,weightedEval y W R i)=0:=by
    rw [row_apply] at eq
    convert eq using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [weightedEval_apply,eval_pow,eval_mul,R,y]
    ring
  rw [ev,show R*Q=(H*Q)^2 by dsimp only [R];ring] at rn
  have pos:=RKCert.OrderedGram.pow_square_pos 0 (H*Q) (mul_ne_zero hn qn)
  rw [pow_zero,one_mul] at pos
  exact pos.ne' rn.symm

theorem LocalLinearBand.low_profile_zero (B:LocalLinearBand A b r U τ)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)
    (Q P:K[X])(dq:Q.natDegree≤4)(dp:P=0∨P.natDegree+(r+1)≤4)
    {u:Vec K 26}(uU:u∈U)
    (preserve:∀v∈U,f*v∈U)
    (fit:weightedEval (mirror A) τ Q=τ*f)
    (rep:b*f=u+weightedEval (mirror A) τ P):
    Q=0:=by
  by_contra qn
  have rr:r≤2:=by rcases B.short with e|e <;> omega
  have dp3:P.natDegree≤3:=by
    rcases dp with z|p
    · simp [z]
    · omega
  have Ppay:12+P.natDegree≤15-r:=by
    rcases dp with z|p
    · simpa [z] using (show 12≤15-r by omega)
    · omega
  obtain ⟨v,vU,h⟩:=B.local_contrast_clean Q P uU preserve fit rep
  have fail (H:K[X])(hn:H≠0)(dH:H.natDegree≤2):weightedEval (mirror A) (localContrast A b f Q) H∉U:=
    localized_contrast_not_base B ho Q P H vU qn hn dq dH dp3 h
  obtain ⟨a,an,left⟩:=B.local_contrast_port ha ho Q P X vU fit preserve h (fail X X_ne_zero (by simp)) 2
    (by rw [natDegree_X];omega) (by rw [natDegree_X];omega)
  have a0:a≠0:=by simpa only [eval_X] using an
  let G:K[X]:=X*(X-C a)
  have Gd:G.natDegree≤2:=natDegree_mul_le.trans (by rw [natDegree_X,natDegree_X_sub_C])
  have Gn:G≠0:=mul_ne_zero X_ne_zero (X_sub_C_ne_zero a)
  obtain ⟨z,zn,right⟩:=B.local_contrast_port ha ho Q P G vU fit preserve h (fail G Gn Gd) 1 (by omega) (by omega)
  have ne:z*(z-a)≠0:=by simpa only [G,eval_mul,eval_sub,eval_X,eval_C] using zn
  exact qn (ordered_quartic_physical Q dq a0 (mul_ne_zero_iff.mp ne).1
    (sub_ne_zero.mp (mul_ne_zero_iff.mp ne).2) left right)

theorem LocalLinearBand.grade_four_hidden (B:LocalLinearBand A b r U τ)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17):
    zeroSpace A 4≤reverseHidden b τ U:=by
  intro f hf
  have rr:r≤2:=by rcases B.short with e|e <;> omega
  obtain ⟨Q,dQ,fit⟩:=B.head_trace ho hf (by omega)
  obtain ⟨u,hu,P,dp,rep⟩:=B.weight_trace ho hf (by decide)
  have q0:=B.low_profile_zero ha ho Q P dQ dp hu
    (fun v hv=>B.mul_base ho (by omega) hf hv) fit rep
  have v0:τ*f=0:=by rw [←fit,q0,map_zero]
  exact B.hidden_of_zero_profile ho (by omega) hf v0

end
end RKCert.Paired.ReverseHull

