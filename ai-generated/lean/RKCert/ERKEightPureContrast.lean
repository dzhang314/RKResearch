module
public import RKCert.OrderTwelveChronologicalContrast
public import RKCert.OrderedIntervalMoments

@[expose] public section
/-! # The unmarked chronological multiplier test at every affordable grade -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint
open RKCert.Paired.OrderTwelve Polynomial
variable {K:Type*} [Field K] [CharZero K] {s p j g H n:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w v:Vec K (s+1)}

omit [CharZero K] in
theorem actual_weighted_grade (ho:HasTreeOrderAtLeast A b p) (R:K[X])
    (pay:R.natDegree+1≤p) (hv:v∈zeroSpace A j) :
    weightedEval (nodes A) v R∈zeroSpace A (j+R.natDegree) := by
  have ev : weightedEval (nodes A) v R=v*evalNodes A R := by ext i; simp [evalNodes,mul_comm]
  rw [ev]
  exact zeroSpace_mul_treeSpace ho pay hv (evalNodes_mem_treeSpace A R le_rfl)

/-- The first genuinely unmatched joint clock/multiplier block detects the
primitive. Repetition of physical clock values, including within the first
prefix, does not affect the assertion. -/
theorem actual_pure_multiplier_contrast (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (hpay:H+1≤p) (hsep:Separated A H)
    (hU:U.map (diag (nodes A))≤U) (hV:U.map (diag v)≤U)
    (hUF:U≤zeroSpace A g) (hG:g+1≤H) (hv:v∈zeroSpace A j)
    (chart:zeroSpace A H≤chain (diag (nodes A)) U w n)
    (P Q:K[X]) (hP:P≠0) (hQ:Q≠0) (dp:P.natDegree≤j) (dq:j+Q.natDegree≤H)
    (fit:v*w-weightedEval (nodes A) w P∈U) :
    ∃ k:Fin (s+1), Q.eval (nodes A k)≠0 ∧
       ∀ R:K[X],j+Q.natDegree+R.natDegree+1≤H→
        (Paired.primitive ((R*Q)*P)).eval (nodes A k)=0 := by
  classical
  let c := nodes A
  let z := evalNodes A (Q*P)-weightedEval c v Q
  have znot : z∉U := by
    intro hn
    have pure := zeroSpace_mono A dq (actual_weighted_grade ho Q (by omega) hv)
    change weightedEval c v Q∈zeroSpace A H at pure
    have sum := (zeroSpace A H).add_mem (zeroSpace_mono A (show g≤H by omega) (hUF hn)) pure
    exact mul_ne_zero hQ hP (hsep _ (natDegree_mul_le.trans (by omega))
      (by simpa only [z,sub_add_cancel] using sum))
  obtain ⟨tag,tagEq,tagC⟩:=joint_labels hU hV
  obtain ⟨k,m,hm,before,bad⟩:=first_unmatched_block tag z U tagC znot
  let t:=c k
  let τ:=v k
  let z0:=Q.eval t*(P.eval t-τ)
  have zlocal (i:Fin (s+1)) (hi:tag i=tag k) : z i=z0 := by
    obtain ⟨hc,hv⟩:=(tagEq i k).mp hi
    simp only [z,Pi.sub_apply,evalNodes_apply,weightedEval_apply,eval_mul]
    change Q.eval (c i)*P.eval (c i)-Q.eval (c i)*v i=z0
    change c i=c k at hc
    rw [hc,hv]
    dsimp [z0,t,τ];ring
  have hz:z0≠0 := by
    intro he
    exact bad ⟨0,U.zero_mem,fun i _ hi=>by rw [zlocal i hi,he];rfl⟩
  have mismatch : τ≠P.eval t := fun e=>(mul_ne_zero_iff.mp hz).2 (sub_eq_zero.mpr e.symm)
  refine ⟨k,(mul_ne_zero_iff.mp hz).1,fun R budget=>?_⟩
  let S:=R*Q
  let F:=S*P
  let D:=H-1
  have hD:D+1=H:=by dsimp [D];omega
  let f := contrastResidual A v P S+mat A (weightedEval c m R)
  have dS:S.natDegree≤R.natDegree+Q.natDegree:=natDegree_mul_le
  have qR:weightedEval c v S∈zeroSpace A D :=
    zeroSpace_mono A (by omega) (actual_weighted_grade ho S (by omega) hv)
  have mR:weightedEval c m R∈U:=by
    have E : weightedEval c m R=fun i=>R.eval (c i)*m i := by ext i;simp
    rw [E]
    exact poly_preserves hU R m hm
  have paid:f∈zeroSpace A H:=by
    rw [←hD]
    exact (zeroSpace A (D+1)).add_mem
      (contrast_residual_grade P S (natDegree_mul_le.trans (by omega)) qR)
      (mat_zeroSpace_charZero A D (zeroSpace_mono A (by omega) (hUF mR)))
  have loc (i:Fin (s+1)) (hi:i.val<k.val+1) :
      f i=(Paired.primitive F).eval (c i) := by
    have eq : mat A (evalNodes A F-weightedEval c v S) i=mat A (weightedEval c m R) i := by
      apply strictlyCausal_mat ha
      intro l hl
      have hl' : l<k:=by change l.val < i.val at hl;change l.val < k.val;omega
      have b0:=before l hl'
      simp only [z,Pi.sub_apply,evalNodes_apply,weightedEval_apply,eval_mul] at b0
      simp only [Pi.sub_apply,evalNodes_apply,weightedEval_apply]
      change F.eval (c l)-S.eval (c l)*v l=R.eval (c l)*m l
      simp only [F,S,eval_mul]
      change m l=Q.eval (c l)*P.eval (c l)-Q.eval (c l)*v l at b0
      rw [b0];ring
    change contrastResidual A v P S i+mat A (weightedEval c m R) i=_
    rw [contrastResidual_apply,Pi.sub_apply,evalNodes_apply,eq,sub_add_cancel]
  by_contra fn
  have nloc:=joint_chain_core hU hV fit mismatch (chart paid)
  let α:=z0/(Paired.primitive F).eval t
  apply bad
  refine ⟨α • fiber v τ (fiber c t f),U.smul_mem _ nloc,fun i hi eq=>?_⟩
  obtain ⟨hci,hvi⟩:=(tagEq i k).mp eq
  change c i=t at hci
  change v i=τ at hvi
  simp only [Pi.smul_apply,smul_eq_mul,fiber,hci,hvi,ite_true]
  rw [loc i hi,hci,div_mul_cancel₀ _ fn,zlocal i eq]

end RKCert.Paired.FiniteMidpoint

namespace RKCert.Endpoint
open RKCert.Paired Polynomial
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A genuinely oriented one-endpoint weighted Gram: valid also for a
negative primitive endpoint. This is a formal, not analytic, integral. -/
theorem primitive_x_square_pos (P:K[X]) (hP:P≠0) (u:K) (hu:u≠0) :
    0<(Paired.primitive (X*P^2)).eval u := by
  have h:=RKCert.OrderedGram.affine_substitution (X*P^2) 0 u
  let T : K[X] := P.comp (C u*X)
  have e : (X*P^2).comp (C (u-0)*X+C 0)=u • (X*T^2) := by
    simp [T,mul_comp,pow_comp,Polynomial.smul_eq_C_mul,mul_assoc]
  have z : (Paired.primitive (X*P^2)).eval 0=0 := by
    rw [←coeff_zero_eq_eval_zero,primitive_coeff_zero]
  rw [e,map_smul,eval_smul,smul_eq_mul,z,sub_zero,sub_zero] at h
  have t0 : T≠0 := by
    simpa [T] using RKCert.OrderedGram.affine_comp_ne_zero hP 0 u hu
  have pos:=RKCert.OrderedGram.pow_square_pos 1 T t0
  change 0<(Paired.primitive (X^1*T^2)).eval 1 at pos
  rw [pow_one] at pos
  rw [h,←mul_assoc]
  exact mul_pos (mul_self_pos.mpr hu) pos

/-- Existing 3+2 quartic gate in native polynomial primitive coordinates. -/
theorem ordered_quartic_physical (P:K[X]) (dp:P.natDegree≤4) {u v:K}
    (hu:u≠0) (hv:v≠0) (hvu:v≠u)
    (first:∀R:K[X],R.natDegree≤2→(Paired.primitive (R*(X*P))).eval u=0)
    (second:∀R:K[X],R.natDegree≤1→(Paired.primitive (R*(X*(X-C u)*P))).eval v=0) :
    P=0 := by
  let _ : DecidableEq K := Classical.decEq K
  let e := toFn 5 P
  have repr : ofFn 5 e=P:=ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  have native (x:K) (k:ℕ) : (Paired.primitive (X^k*P)).eval x=moment e x k :=
    (congrArg (fun Z:K[X]=>(Paired.primitive (X^k*Z)).eval x) repr.symm).trans
      (primitive_monomial_moment e x k)
  have f (k:Fin 3) : moment e u (k.val+1)=0 := by
    have he:=first (X^k.val) (by rw [natDegree_X_pow];have :=k.isLt;omega)
    have eq : (X:K[X])^k.val*(X*P)=X^(k.val+1)*P:=by rw [pow_succ];ring
    rw [eq,native] at he
    exact he
  have g (k:Fin 2) : moment e v (k.val+2)=u*moment e v (k.val+1) := by
    have he:=second (X^k.val) (by rw [natDegree_X_pow];have :=k.isLt;omega)
    have eq : (X:K[X])^k.val*(X*(X-C u)*P)=X^(k.val+2)*P-u • (X^(k.val+1)*P) := by
      rw [Polynomial.smul_eq_C_mul,pow_add,pow_succ _ k.val];ring
    rw [eq,map_sub,map_smul,eval_sub,eval_smul,native,native,smul_eq_mul] at he
    exact sub_eq_zero.mp he
  have M : twoTests (EndpointPhysical.rescale e u) (v/u) 3 :=
    EndpointPhysical.normalize hu ⟨f,sub_eq_zero.mpr (g 0),sub_eq_zero.mpr (g 1)⟩
  have z := ordered_quartic_three_two _ _ (div_ne_zero hv hu)
    (fun eq=>hvu ((div_eq_one_iff_eq hu).mp eq)) M
  rw [←repr,(EndpointPhysical.rescale_eq_zero_iff e hu).mp z,map_zero]

end RKCert.Endpoint
