module
public import RKCert.ERKOrder13FourKnots
public import RKCert.OrderTwelveChronologicalContrast

@[expose] public section
/-! # Full-odd joint-block multiplier contrasts with no seventh-grade leakage
The core need not be a mask algebra. Native clock and multiplier invariance
suffice to localize the first quotient mismatch. True seventh-grade purity
then buys the three-plus-two primitive tests without any factor arithmetic. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Paired.OrderTwelve RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w v:Vec K (s+1)} {G P:K[X]}
set_option maxHeartbeats 3000000

theorem joint_thirteen_knot (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 r U w G)
    (hv:U.map (diag v)≤U) (v3:v∈zeroSpace A 3) (pn:P≠0) (pd:P.natDegree≤3)
    (fit:v*w-weightedEval (nodes A) w P∈U)
    (Q:K[X]) (qn:Q≠0) (qd:Q.natDegree≤3) :
    ∃ k:Fin (s+1), Q.eval (nodes A k)≠0∧P.eval (nodes A k)≠0∧
      ∀ R:K[X],(R*Q).natDegree≤3→(Paired.primitive ((R*Q)*P)).eval (nodes A k)=0 := by
  classical
  let c := nodes A
  let z := evalNodes A (Q*P)-weightedEval c v Q
  have grade (B:K[X]) (hd:B.natDegree≤3) : weightedEval c v B∈zeroSpace A 6 := by
    have e : weightedEval c v B=v*evalNodes A B := by
      ext j
      simp [weightedEval_apply,evalNodes,mul_comm,c]
    rw [e]
    exact zeroSpace_mono A (by omega)
      (zeroSpace_mul_treeSpace ho (by omega) v3 (evalNodes_mem_treeSpace A B le_rfl))
  have core5 : U≤zeroSpace A 5 := fun _ hu=>tail_zero_iff.mp (C.marked.core hu)
  have zd : (Q*P).natDegree≤6 := natDegree_mul_le.trans (by omega)
  have znot : z∉U := by
    intro h
    have Z := zeroSpace_mono A (by decide : 5≤6) (core5 h)
    have hg := (zeroSpace A 6).add_mem Z (grade Q qd)
    have he : evalNodes A (Q*P)∈zeroSpace A 6 := by simpa only [z,sub_add_cancel] using hg
    exact mul_ne_zero qn pn (separated_plus S M _ zd (tail_zero_iff.mpr he))
  obtain ⟨tag,tagEq,tagC⟩:=joint_labels C.marked.stable hv
  obtain ⟨k,p,hp,before,bad⟩:=first_unmatched_block tag z U tagC znot
  let t:=c k
  let τ:=v k
  let Z0:=Q.eval t*(P.eval t-τ)
  have zlocal (j:Fin (s+1)) (hj:tag j=tag k) : z j=Z0 := by
    obtain ⟨hc,hv⟩:= (tagEq j k).mp hj
    simp [z,c,evalNodes,weightedEval_apply] at hc hv ⊢
    rw [hc,hv]
    dsimp [Z0,t,τ,c];ring
  have zd0 : Z0≠0 := by
    intro e
    apply bad
    exact ⟨0,U.zero_mem,fun j _ hj=>by rw [zlocal j hj,e];rfl⟩
  have q0 : Q.eval t≠0 := (mul_ne_zero_iff.mp zd0).1
  have mismatch : τ≠P.eval t := fun e => (mul_ne_zero_iff.mp zd0).2 (sub_eq_zero.mpr e.symm)
  have restrict_Z {z':Vec K (s+1)} (h:z'∈zeroSpace A 7) :
      fiber v τ (fiber c t z')∈U := by
    rw [order13_full_exact_F7 ha ho C] at h
    exact joint_chain_core C.marked.stable hv fit mismatch h
  have cannot (y:Vec K (s+1)) (hy:y∈zeroSpace A 7) (ξ:K)
      (vals:∀ j:Fin (s+1),j.val<k.val+1→tag j=tag k→y j=ξ) : ξ=0 := by
    by_contra nz
    apply bad
    refine ⟨(Z0/ξ) • fiber v τ (fiber c t y),U.smul_mem _ (restrict_Z hy),?_⟩
    intro j hj etag
    obtain ⟨hc,hv⟩:=(tagEq j k).mp etag
    have hc' : c j=t := hc
    have hv' : v j=τ := hv
    simp only [Pi.smul_apply,smul_eq_mul,fiber,hv',hc',ite_true]
    rw [vals j hj etag,div_mul_cancel₀ _ nz,zlocal j etag]
  have zero : τ=0 := cannot v (zeroSpace_mono A (by decide) v3) τ
    (fun j _ ej=>(tagEq j k).mp ej |>.2)
  have pn0 : P.eval t≠0 := by intro he;exact mismatch (by rw [zero,he])
  refine ⟨k,q0,pn0,?_⟩
  intro R dr
  let D:=R*Q
  change D.natDegree≤3 at dr
  let F:=D*P
  let y:=contrastResidual A v P D+mat A (weightedEval c p R)
  have wp : weightedEval c p R∈U := by
    have h := poly_preserves C.marked.stable R p hp
    have eq : weightedEval c p R=fun j=>R.eval (c j)*p j := by ext j;simp
    rwa [eq]
  have ap : mat A (weightedEval c p R)∈zeroSpace A 7 :=
    zeroSpace_mono A (by decide) (mat_zeroSpace_charZero A 5 (core5 wp))
  have main : contrastResidual A v P D∈zeroSpace A 7 :=
    contrast_residual_grade P D (q:=6) (natDegree_mul_le.trans (by omega)) (grade D dr)
  have hy:y∈zeroSpace A 7 := Submodule.add_mem _ main ap
  apply cannot y hy ((Paired.primitive F).eval t)
  intro j hj ej
  have hc : c j=t := (tagEq j k).mp ej |>.1
  have eq : mat A (evalNodes A F-weightedEval c v D) j=mat A (weightedEval c p R) j := by
    apply strictlyCausal_mat ha
    intro m hm
    have hm' : m<k := by change m.val<j.val at hm;change m.val<k.val;omega
    have hpm := before m hm'
    change evalNodes A F m-weightedEval c v D m=weightedEval c p R m
    simp only [weightedEval_apply,evalNodes,F,D,eval_mul]
    simp only [z,Pi.sub_apply,evalNodes,weightedEval_apply,eval_mul] at hpm
    rw [hpm];ring
  dsimp only [y]
  rw [Pi.add_apply,contrastResidual_apply,Pi.sub_apply]
  change (Paired.primitive F).eval (c j)-mat A (evalNodes A F-weightedEval c v D) j+
    mat A (weightedEval c p R) j=_
  rw [eq,sub_add_cancel,hc]

theorem joint_thirteen_cubic_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 r U w G)
    (hv:U.map (diag v)≤U) (v3:v∈zeroSpace A 3) (pn:P≠0) (pd:P.natDegree≤3)
    (fit:v*w-weightedEval (nodes A) w P∈U) : False := by
  have test (R:K[X]) (rn:R≠0) (rd:R.natDegree≤3) (δ:ℕ) (hd:δ≤1) (eq:(X:K[X])^δ*P=X*R) : False := by
    let Q1 : K[X]:=X^δ
    have d1:Q1.natDegree=δ:=natDegree_X_pow _
    obtain ⟨i,qi,pi,ui⟩:=joint_thirteen_knot ha ho S M C hv v3 pn pd fit Q1 (pow_ne_zero _ X_ne_zero) (by omega)
    let u:=nodes A i
    have ufit : u*R.eval u≠0 := by
      have h:=(mul_ne_zero qi pi)
      rw [←eval_mul,show Q1*P=X*R from eq,eval_mul,eval_X] at h
      exact h
    let Q2:K[X]:=Q1*(X-Polynomial.C u)
    have n2:Q2≠0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) (X_sub_C_ne_zero _)
    have d2:Q2.natDegree=δ+1 := by
      change (Q1*(X-Polynomial.C u)).natDegree=δ+1
      rw [natDegree_mul (show Q1≠0 from pow_ne_zero _ X_ne_zero) (X_sub_C_ne_zero _),d1,natDegree_X_sub_C]
    obtain ⟨j,qj,pj,uj⟩:=joint_thirteen_knot ha ho S M C hv v3 pn pd fit Q2 n2 (by omega)
    let vv:=nodes A j
    have e2:Q2*P=X*(X-Polynomial.C u)*R := by
      calc
        _ = (X-Polynomial.C u)*(Q1*P) := by dsimp [Q2];ring
        _ = _ := by rw [show Q1*P=X*R from eq];ring
    have vfit : vv*(vv-u)*R.eval vv≠0 := by
      have h:=mul_ne_zero qj pj
      rw [←eval_mul,e2,eval_mul,eval_mul,eval_X,eval_sub,eval_X,eval_C] at h
      exact h
    have J : KnotPair R (0:K[X]) 8 u vv := by
      refine ⟨(mul_ne_zero_iff.mp ufit).1,(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp vfit).1).1,
        sub_ne_zero.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp vfit).1).2,
        (mul_ne_zero_iff.mp ufit).2,(mul_ne_zero_iff.mp vfit).2,eval_zero,eval_zero,?_,?_⟩
      · intro k hk
        have e:=ui (X^k) (natDegree_mul_le.trans (by rw [d1,natDegree_X_pow];omega))
        rwa [mul_assoc,show Q1*P=X*R from eq] at e
      · intro k hk
        have e:=uj (X^k) (natDegree_mul_le.trans (by rw [d2,natDegree_X_pow];omega))
        rwa [mul_assoc,e2] at e
    exact rn (cubic_no_profile (by decide) J rd)
  by_cases p0:P.eval 0=0
  · obtain ⟨R,e⟩ : (X:K[X])∣P := by simpa using (dvd_iff_isRoot (a:=(0:K))).mpr p0
    have rn:R≠0 := fun h=>pn (by rw [e,h,mul_zero])
    have rd:R.natDegree≤3 := by rw [e,natDegree_X_mul rn] at pd;omega
    exact test R rn rd 0 (by decide) (by rwa [pow_zero,one_mul])
  · exact test P pn pd 1 (by decide) (by rw [pow_one])

end RKCert.Paired.FiniteMidpoint
