module
public import RKCert.ERKOddHiddenTerminal
public import RKCert.ERKOddFixedRadauTable

@[expose] public section
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.FiniteMidpoint RKCert.Paired.Clock RKCert.Endpoint RKCert.OrderedGram Polynomial
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s p:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
noncomputable section
set_option maxHeartbeats 1600000

theorem reverse_contrast_moment (ho:HasTreeOrderAtLeast A b p)(Q P H:K[X])
    (qpay:Q.natDegree+H.natDegree+2≤p)(ppay:P.natDegree+H.natDegree+3≤p) :
    (∑i,weightedEval (mirror A) (reverseContrast A b Q P) H i)=(primitive (H*(X*Q))).eval 1:=by
  have dP:(H*P).natDegree+3≤p:=by
    have h:=natDegree_mul_le (p:=H) (q:=P);omega
  have dQ:(H*(X*Q)).natDegree+1≤p:=by
    have h:=natDegree_mul_le (p:=H) (q:=X*Q)
    have i:=natDegree_mul_le (p:=X) (q:=Q)
    rw [natDegree_X] at i;omega
  rw [reverseContrast_weighted]
  simp only [Pi.sub_apply,Finset.sum_sub_distrib,reflected_scalar_budget ho _ dQ,
    seed_eval_mass ho _ dP,sub_zero,formalPrimitive_eq_treePrimitive]

theorem reverse_contrast_true_support {Q P:K[X]}{f:Vec K (s+1)}
    (qfit:∀i,backSeed2 A b i*f i=Q.eval (mirror A i)*backSeed2 A b i)
    (pfit:∀i,mirror A i*b i*f i=P.eval (mirror A i)*backSeed2 A b i)
    (i:Fin (s+1))(act:reverseContrast A b Q P i≠0) :
    backSeed2 A b i=0 ∧ mirror A i≠0 ∧ b i≠0 ∧ Q.eval (mirror A i)≠0 ∧ f i=0:=by
  have off:backSeed2 A b i=0:=by
    by_contra z
    have he:=qfit i
    rw [mul_comm (Q.eval _)] at he
    have eq:=mul_left_cancel₀ z he
    have ph:=pfit i
    rw [eq] at ph
    apply act
    simp only [reverseContrast,Pi.sub_apply,weightedEval_apply,eval_mul,eval_X]
    linear_combination ph
  have pf:=pfit i
  rw [off,mul_zero] at pf
  have wt:mirror A i*(Q.eval (mirror A i))*b i≠0:=by
    simpa only [reverseContrast,Pi.sub_apply,weightedEval_apply,eval_mul,eval_X,off,mul_zero,sub_zero] using act
  obtain ⟨yq,bi⟩:=mul_ne_zero_iff.mp wt
  obtain ⟨y,q⟩:=mul_ne_zero_iff.mp yq
  exact ⟨off,y,bi,q,(mul_eq_zero.mp pf).resolve_left (mul_ne_zero y bi)⟩

omit [IsStrictOrderedRing K] in
theorem reverse_contrast_vanishes (W:Vec K (s+1))(H:K[X])
    (h:∀a∈headSites (mirror A) W,H.eval a=0) :
    (∑i,weightedEval (mirror A) W H i)=0:=by
  apply Finset.sum_eq_zero
  intro i _
  by_cases e:W i=0
  · simp [e]
  · rw [weightedEval_apply,h _ (headSites_mem i e),zero_mul]

theorem reverse_contrast_first (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)
    (Z:OddZeroReverse A b 8)
    (Q P:K[X])(dQ:Q.natDegree≤5)(dP:P.natDegree≤4)
    (off:∀i,reverseContrast A b Q P i≠0→backSeed2 A b i=0)
    (i:Fin (s+1))(wi:reverseContrast A b Q P i≠0)
    (last:∀l:Fin (s+1),i < l → reverseContrast A b Q P l=0) :
    (primitive (X*Q)).eval (mirror A i)=0:=by
  let Y:=mirror A
  let W:=reverseContrast A b Q P
  let t:=Fin.last s
  have y0:Y t=0:=by change 1-nodes A (Fin.last s)=0;rw [Z.lastNode,sub_self]
  have col:∀k,A k t=0:=fun k=>ha k _ (Fin.le_last k)
  have sup:SupportsComplement A b 8 t:=by
    intro v hv k z
    obtain ⟨R,_,e⟩:=Z.poly_cover (by decide) hv
    rw [←e,weightedEval_apply,z,mul_zero]
  have m:=true_port_eval ho y0 col sup Q P (1:K[X])
    (by rw [natDegree_one];omega) (by rw [natDegree_one];omega) (off i wi)
  have zh:transMat A (weightedEval Y W 1) i=0:=by
    apply causal_transpose ha
    intro k hk
    simp [W,last k (Fin.rev_lt_rev.mp hk)]
  change transMat A (weightedEval Y W 1) i=_ at m
  rw [zh,one_mul] at m
  have bi:b i≠0:=by
    intro bz
    apply wi
    simp [reverseContrast,bz,off i wi]
  exact (mul_eq_zero.mp m.symm).resolve_right bi

/-- No degree-five true reverse contrast at the ordered p17 boundary can
be carried by only three distinct abscissae. The equality case defeats
even arbitrary signed/exterior configurations by the fixed Radau factor
gate, not by a choice of positive tableau weights. -/
theorem odd17_contrast_four_sites (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)
    (Z:OddZeroReverse A b 8)
    (Q P:K[X])(qn:Q≠0)(dQ:Q.natDegree≤5)(dP:P.natDegree≤4)
    (off:∀i,reverseContrast A b Q P i≠0→backSeed2 A b i=0) :
    4≤(headSites (mirror A) (reverseContrast A b Q P)).card:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let W:=reverseContrast A b Q P
  let Y:=mirror A
  let S:=headSites Y W
  let R:K[X]:=Lagrange.nodal S id
  have rn:R≠0:=Lagrange.nodal_ne_zero
  have dr:R.natDegree=S.card:=Lagrange.natDegree_nodal
  have root(a:K)(av:a∈S):R.eval a=0:=Lagrange.eval_nodal_at_node (v:=id) av
  change 4≤S.card
  by_contra! short
  have exact3:S.card=3:=by
    by_contra neq
    have small:S.card≤2:=by omega
    let H:=Q*R^2
    have dh:H.natDegree≤10:=by
      have h:=natDegree_mul_le (p:=Q) (q:=R^2)
      rw [natDegree_pow,dr] at h
      dsimp only [H];omega
    have mm:=reverse_contrast_moment ho Q P H (by omega) (by omega)
    have van:(∑i,weightedEval Y W H i)=0:=reverse_contrast_vanishes W H
      (fun a av=>by simp [H,root a av])
    rw [van,show H*(X*Q)=X*(Q*R)^2 by dsimp [H];ring] at mm
    have pos:=pow_square_pos 1 (Q*R) (mul_ne_zero qn rn)
    rw [pow_one] at pos
    exact pos.ne' mm.symm
  have dp:(X*(Q*R)).natDegree≤9:=by
    have h:=natDegree_mul_le (p:=Q) (q:=R)
    have k:=natDegree_mul_le (p:=X) (q:=Q*R)
    rw [natDegree_X] at k;omega
  have mom(k:Fin 8):scalarMoment (X*(Q*R)) k.val=0:=by
    let H:K[X]:=X^k.val*R
    have dh:H.natDegree≤10:=by
      have h:=natDegree_mul_le (p:=(X:K[X])^k.val) (q:=R)
      rw [natDegree_X_pow,dr] at h
      dsimp only [H];have:=k.isLt;omega
    have van:(∑i,weightedEval Y W H i)=0:=reverse_contrast_vanishes W H (fun a av=>by simp [H,root a av])
    have m:=reverse_contrast_moment ho Q P H (by omega) (by omega)
    rw [van,show H*(X*Q)=X^k.val*(X*(Q*R)) by dsimp [H];ring] at m
    exact m.symm
  obtain ⟨a,e⟩:=meshFull8_decode (X*(Q*R)) dp (by simp) mom
  have an:a≠0:=by
    intro ez
    rw [ez,zero_smul] at e
    exact (mul_ne_zero X_ne_zero (mul_ne_zero qn rn)) e
  have div:Q∣(odd8:K[X]):=by
    refine ⟨C a⁻¹*(X*R),?_⟩
    calc
      _=C a⁻¹*(a • (odd8:K[X])):=by rw [Polynomial.smul_eq_C_mul,←mul_assoc,←C_mul,inv_mul_cancel₀ an,C_1,one_mul]
      _=_:=by rw [←e];ring
  let I:=Finset.univ.filter (fun i:Fin (s+1)=>W i≠0)
  have ne:I.Nonempty:=by
    obtain ⟨r,hr⟩:=Finset.card_pos.mp (by omega:0<S.card)
    obtain ⟨i,hi,_⟩:=Finset.mem_image.mp hr
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩⟩
  let i:=I.max' ne
  have wi:W i≠0:=(Finset.mem_filter.mp (I.max'_mem ne)).2
  have last:∀l:Fin (s+1),i < l →W l=0:=by
    intro l hl
    by_contra hz
    exact (not_le_of_gt hl) (I.le_max' _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩))
  have un:Y i≠0:=by
    intro y0;apply wi
    simp [W,reverseContrast,show mirror A i=0 from y0,off i wi]
  have g:(odd8:K[X]).eval (Y i)=0:=by
    have en:=congrArg (eval (Y i)) e
    have rr:=root _ (headSites_mem i wi)
    rw [eval_mul,eval_mul,rr,mul_zero,mul_zero,eval_smul,smul_eq_mul] at en
    exact (mul_eq_zero.mp en.symm).resolve_left an
  exact RKCert.RadauEight.FirstMoment.radau8_first_moment div dQ un g (reverse_contrast_first ha ho Z Q P dQ dP off i wi last)
end
end RKCert.Paired.ReverseHull
