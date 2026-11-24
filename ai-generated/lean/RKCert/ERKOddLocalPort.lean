module
public import RKCert.ERKOddLocalContrast

@[expose] public section
/-! # The genuine reverse chronological low-degree primitive witnesses -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ f:Vec K 26}{r:ℕ}{U:Submodule K (Vec K 26)}
noncomputable section

private theorem local_weighted_base (B:LocalLinearBand A b r U τ)
    {u:Vec K 26}(hu:u∈U)(T:K[X]):weightedEval (mirror A) u T∈U:=by
  have e:weightedEval (mirror A) u T=(fun i=>T.eval (mirror A i)*u i):=by
    ext i;exact weightedEval_apply _ _ _ _
  rw [e]
  exact Clock.poly_preserves B.clock T u hu

private theorem local_trans_base (B:LocalLinearBand A b r U τ)
    (ho:HasTreeOrderAtLeast A b 17){u:Vec K 26}(hu:u∈U):
    transMat A u∈annih (treeSpace A 8):=by
  have rr:r≤2:=by rcases B.short with e|e <;> omega
  apply mem_annih.mpr
  intro x hx
  rw [row_flip_mat]
  exact mem_annih.mp (B.base_annih ho hu) _ (treeSpace_mono A (by omega:8+1≤16-r) (mat_treeSpace A 8 hx))

private theorem local_trans_head (B:LocalLinearBand A b r U τ) (T:K[X])
    (pay:9+T.natDegree≤15-r):transMat A (weightedEval (mirror A) τ T)∈annih (treeSpace A 8):=by
  apply mem_annih.mpr
  intro x hx
  rw [row_flip_mat]
  have z:=mem_annih.mp B.paid _ (treeSpace_mono A pay
    (treeSpace_mul (mat_treeSpace A 8 hx) (mirror_eval_in_tree (A:=A) T (Nat.le_refl _))))
  rw [row_apply] at z ⊢
  convert z using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [weightedEval_apply,Pi.mul_apply]
  ring

private theorem local_functional_kills (B:LocalLinearBand A b r U τ) {ℓ v:Vec K 26}
    (kill:ℓ∈annih U)(offs:∀i,ℓ i≠0→τ i=0)(hv:v∈annih (treeSpace A 8)):
    row ℓ v=0:=by
  obtain ⟨u,hu,P,_,e⟩:=B.representation hv
  rw [e,map_add,mem_annih.mp kill _ hu,zero_add,row_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases z:ℓ i=0
  · rw [z,zero_mul]
  · rw [weightedEval_apply,offs i z,mul_zero,mul_zero]

omit [IsStrictOrderedRing K] in
private theorem local_constant_functional {ℓ v:Vec K 26}{a:K}
    (site:∀i,ℓ i≠0→mirror A i=a)(T:K[X]):
    row ℓ (weightedEval (mirror A) v T)=T.eval a*row ℓ v:=by
  simp only [row_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases z:ℓ i=0
  · simp [z]
  rw [weightedEval_apply,site i z]
  ring

omit [IsStrictOrderedRing K] in
private theorem local_prefix_value (ha:StrictLower A) {H:K[X]}{W ℓ u:Vec K 26}{i:Fin 26}
    (D:ReversePrefixDetector (mirror A) f (weightedEval (mirror A) W H) U i ℓ u)
    (R:K[X]):
    row ℓ (transMat A (weightedEval (mirror A) W (R*H)))=
      row ℓ (transMat A (weightedEval (mirror A) u R)):=by
  simp only [row_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases z:ℓ k=0
  · simp [z]
  congr 1
  have h:(transMat A (weightedEval (mirror A) W (R*H)-weightedEval (mirror A) u R)) k=0:=by
    apply causal_transpose ha
    intro j jlt
    have kj:k<j:=Fin.rev_lt_rev.mp jlt
    have ij:i<j:=(D.allowed k z).1.trans_lt kj
    have e:=D.matchEarlier j ij
    rw [weightedEval_apply] at e
    simp only [weightedEval_apply,Pi.sub_apply,eval_mul]
    rw [←e]
    ring
  simpa only [map_sub,Pi.sub_apply,sub_eq_zero] using h

/-- Read a genuine primitive test at the clock of a reverse-prefix block.
It is a nonzero weighted prefix functional, not a proposed new stage. -/
theorem LocalLinearBand.local_contrast_port (B:LocalLinearBand A b r U τ)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)
    (Q P H:K[X]){u:Vec K 26}(uU:u∈U)
    (fit:weightedEval (mirror A) τ Q=τ*f)
    (preserve:∀v∈U,f*v∈U)
    (spec:localContrast A b f Q=weightedEval (mirror A) b Q-weightedEval (mirror A) τ P-u)
    (new:weightedEval (mirror A) (localContrast A b f Q) H∉U)
    (k:ℕ)(qb:10+Q.natDegree+H.natDegree+k≤17)
    (pb:9+P.natDegree+H.natDegree+k≤15-r):
    ∃a:K,H.eval a≠0∧∀R:K[X],R.natDegree≤k→(Paired.primitive (R*(H*Q))).eval a=0:=by
  let y:=mirror A
  let W:=localContrast A b f Q
  let x:=weightedEval y W H
  have inv:U.map (diag f)≤U:=by
    rintro _ ⟨v,hv,rfl⟩
    have e:diag f v=f*v:=by ext i;simp [diag_apply]
    rw [e];exact preserve v hv
  obtain ⟨i,ℓ,v,D⟩:=reverse_prefix_detector B.clock inv new
  let a:=y i
  have same(j:Fin 26)(nz:ℓ j≠0):y j=a:=(D.allowed j nz).2.1
  have support:∃ j:Fin 26,ℓ j*x j≠0:=by
    by_contra! h
    exact D.detects (by rw [row_apply];exact Finset.sum_eq_zero (fun i _=>h i))
  obtain ⟨j,jx⟩:=support
  have lj:ℓ j≠0:=(mul_ne_zero_iff.mp jx).1
  have xj:x j≠0:=(mul_ne_zero_iff.mp jx).2
  have xe:x j=H.eval (y j)*W j:=weightedEval_apply _ _ _ _
  have Hw:H.eval a≠0:=by rw [xe,same j lj] at xj;exact (mul_ne_zero_iff.mp xj).1
  have Wj:W j≠0:=by rw [xe] at xj;exact (mul_ne_zero_iff.mp xj).2
  have fj:f j=0:=by
    by_contra f0
    apply Wj
    change localContrast A b f Q j=0
    rw [localContrast_apply,ite_eq_right f0]
  have fa:f i=0:=(D.allowed j lj).2.2.symm.trans fj
  have Q0:Q.eval a≠0:=by
    rw [show W j=localContrast A b f Q j from rfl,localContrast_apply,ite_eq_left fj,show mirror A j=a from same j lj] at Wj
    exact (mul_ne_zero_iff.mp Wj).1
  have zs(k:Fin 26)(nz:ℓ k≠0):τ k=0:=by
    have h:=congrFun fit k
    simp only [weightedEval_apply,Pi.mul_apply,(D.allowed k nz).2.2,fa,mul_zero] at h
    rw [show mirror A k=a from same k nz] at h
    exact (mul_eq_zero.mp h).resolve_left Q0
  have filt:row ℓ x=(H.eval a*Q.eval a)*row ℓ b:=by
    simp only [row_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    by_cases nz:ℓ k=0
    · simp [nz]
    change ℓ k*weightedEval y W H k=_
    rw [weightedEval_apply,same k nz,show W k=localContrast A b f Q k from rfl,localContrast_apply,
      ite_eq_left ((D.allowed k nz).2.2.trans fa),show mirror A k=a from same k nz]
    ring
  have lbs:row ℓ b≠0:=by intro h;exact D.detects (by rw [filt,h,mul_zero])
  refine ⟨a,Hw,?_⟩
  intro R dR
  have zero:=local_prefix_value ha (H:=H) D R
  rw [local_functional_kills B D.kills zs (local_trans_base B ho (local_weighted_base B D.previous R))] at zero
  let S:=R*(H*Q)
  let T:=R*(H*P)
  have sd:S.natDegree≤R.natDegree+H.natDegree+Q.natDegree:=by
    have a:=natDegree_mul_le (p:=R) (q:=H*Q)
    have h:=natDegree_mul_le (p:=H) (q:=Q)
    dsimp only [S];omega
  have td:T.natDegree≤R.natDegree+H.natDegree+P.natDegree:=by
    have a:=natDegree_mul_le (p:=R) (q:=H*P)
    have h:=natDegree_mul_le (p:=H) (q:=P)
    dsimp only [T];omega
  have DQ:transMat A (weightedEval y b S)-weightedEval y b (formalPrimitive S)∈annih (treeSpace A 8):=
    primitive_annihilator_paid ho S (by omega)
  have DT:transMat A (weightedEval y τ T)∈annih (treeSpace A 8):=local_trans_head B T (by omega)
  have DU:transMat A (weightedEval y u (R*H))∈annih (treeSpace A 8):=
    local_trans_base B ho (local_weighted_base B uU _)
  have es:weightedEval y W (R*H)=weightedEval y b S-weightedEval y τ T-weightedEval y u (R*H):=by
    ext j
    rw [show W=localContrast A b f Q from rfl,spec]
    simp only [weightedEval_apply,Pi.sub_apply,eval_mul,S,T,y]
    ring
  change row ℓ (transMat A (weightedEval y W (R*H)))=0 at zero
  rw [es,map_sub,map_sub,map_sub,map_sub,local_functional_kills B D.kills zs DT,
    local_functional_kills B D.kills zs DU,sub_zero,sub_zero] at zero
  have z:=local_functional_kills B D.kills zs DQ
  rw [map_sub,zero,zero_sub,neg_eq_zero,local_constant_functional same,formalPrimitive_eq_treePrimitive] at z
  exact (mul_eq_zero.mp z).resolve_right lbs
end
end RKCert.Paired.ReverseHull

