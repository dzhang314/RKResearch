module
public import RKCert.ERKOrder13PureDispatch
public import RKCert.OrderTwelveChronologicalContrast

@[expose] public section
/-! # The actual marked joint-block detector
This does not assume a mask algebra for the invariant core. A first
unmatched joint block has a constant mode outside the accepted prefix;
all restrictions of the head band on that block lie in the core. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Paired.OrderTwelve
  RKCert.Endpoint RKCert.OrderTwelve Module Polynomial
variable {K:Type*} [Field K] [CharZero K] {s a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w v:Vec K (s+1)} {G P:K[X]}
set_option maxHeartbeats 3600000

noncomputable def jointDifference (A:Fin (s+1)→Fin (s+1)→K) (v:Vec K (s+1))
    (P B:K[X]) : Vec K (s+1) :=
  evalNodes A (B*P)-weightedEval (nodes A) v B

omit [CharZero K] in
@[simp] theorem jointDifference_apply (B:K[X]) (i:Fin (s+1)) :
    jointDifference A v P B i =
      B.eval (nodes A i)*(P.eval (nodes A i)-v i) := by
  simp only [jointDifference,Pi.sub_apply,evalNodes_apply,weightedEval_apply,eval_mul]
  ring

structure FirstMarkedJoint (A:Fin (s+1)→Fin (s+1)→K) (v:Vec K (s+1))
    (U:Submodule K (Vec K (s+1))) (P B:K[X]) (i:Fin (s+1)) : Prop where
  nonzero : jointDifference A v P B i≠0
  earlier : ∃p∈U, ∀j < i, jointDifference A v P B j=p j
  bad : ¬∃p∈U, ∀ j ≤ i,nodes A j=nodes A i→v j=v i→p j=1

theorem FirstMarkedJoint.mul {B:K[X]} {i:Fin (s+1)}
    (D:FirstMarkedJoint A v U P B i) (hs:U.map (diag (nodes A))≤U)
    (L:K[X]) (ln:L.eval (nodes A i)≠0) : FirstMarkedJoint A v U P (L*B) i := by
  obtain ⟨p,hp,matchp⟩:=D.earlier
  refine ⟨?_,⟨weightedEval (nodes A) p L,?_,?_⟩,D.bad⟩
  · rw [jointDifference_apply,eval_mul,mul_assoc,←jointDifference_apply]
    exact mul_ne_zero ln D.nonzero
  · have eq : weightedEval (nodes A) p L = fun j=>L.eval (nodes A j)*p j := by ext j;simp only [weightedEval_apply]
    rw [eq]
    exact poly_preserves hs L p hp
  · intro j hj
    rw [jointDifference_apply,eval_mul,mul_assoc,←jointDifference_apply,matchp j hj,weightedEval_apply]

theorem first_marked_joint_exists
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G)
    (hv:U.map (diag v)≤U) (pn:P≠0) (B:K[X]) (bn:B≠0)
    (bp:(B*P).natDegree≤6) (pay:weightedEval (nodes A) v B∈defectPlus A 1 6) :
    ∃i,FirstMarkedJoint A v U P B i := by
  let z:=jointDifference A v P B
  have no:z∉U := by
    intro h
    have add := (defectPlus A 1 6).add_mem (Fplus_mono A 1 (by decide) (C.marked.core h)) pay
    have ev:evalNodes A (B*P)∈defectPlus A 1 6 := by simpa only [z,jointDifference,sub_add_cancel] using add
    exact mul_ne_zero bn pn (separated_plus S M (B*P) bp ev)
  obtain ⟨tags,eqs,hs⟩:=joint_labels C.marked.stable hv
  obtain ⟨i,p,hp,earlier,bad⟩:=first_unmatched_block tags z U hs no
  have same (j:Fin (s+1)) (h:tags j=tags i) : z j=z i := by
    obtain ⟨hc,hv⟩:=(eqs j i).mp h
    dsimp only [z]
    rw [jointDifference_apply,jointDifference_apply,hc,hv]
  refine ⟨i,?_,⟨p,hp,fun j hj=>(earlier j hj).symm⟩,?_⟩
  · intro zero
    exact bad ⟨0,U.zero_mem,fun j _ h=>by rw [same j h,show z i=0 from zero];rfl⟩
  · rintro ⟨q,hq,loc⟩
    apply bad
    refine ⟨z i • q,U.smul_mem _ hq,?_⟩
    intro j hj he
    obtain ⟨hc,hv⟩:=(eqs j i).mp he
    have jl : j ≤ i := by change j.val ≤ i.val;omega
    rw [Pi.smul_apply,smul_eq_mul,loc j jl hc hv,mul_one,same j he]

omit [CharZero K] in
theorem FirstMarkedJoint.const_zero {B:K[X]} {i:Fin (s+1)}
    (D:FirstMarkedJoint A v U P B i) (C:Chart13 A 1 a r U w G)
    (hv:U.map (diag v)≤U) (fit:v*w-weightedEval (nodes A) w P∈U)
    {n:ℕ} {z:Vec K (s+1)} (hz:z∈chain (diag (nodes A)) U w n)
    (ℓ:K) (val:∀ j ≤ i,nodes A j=nodes A i→v j=v i→z j=ℓ) : ℓ=0 := by
  classical
  by_contra ne
  have mismatch : v i≠P.eval (nodes A i) := by
    intro bad
    exact D.nonzero (by simp only [jointDifference_apply,bad,sub_self,mul_zero])
  have localmem :=joint_chain_core C.marked.stable hv fit mismatch hz
  apply D.bad
  refine ⟨ℓ⁻¹ • fiber v (v i) (fiber (nodes A) (nodes A i) z),U.smul_mem _ localmem,?_⟩
  intro j hj hc hv
  simp only [Pi.smul_apply,smul_eq_mul,fiber,hc,hv,ite_true,val j hj hc hv,inv_mul_cancel₀ ne]

theorem FirstMarkedJoint.off {B:K[X]} {i:Fin (s+1)}
    (D:FirstMarkedJoint A v U P B i) (C:Chart13 A 1 a r U w G)
    (hv:U.map (diag v)≤U) (fit:v*w-weightedEval (nodes A) w P∈U)
    (v5:v∈defectPlus A 1 5) :
    G.eval (nodes A i)=0 ∧ (B*P).eval (nodes A i)≠0 := by
  have v0:v i=0 := by
    rw [C.marked.paid 5 le_rfl (by decide)] at v5
    exact D.const_zero C hv fit v5 _ (fun j _ _ same=>same)
  have hm:=C.meshPaid
  rw [C.marked.edge] at hm
  refine ⟨D.const_zero C hv fit hm _ (fun j _ same _=>by simp only [evalNodes_apply,same]),?_⟩
  have nz:=D.nonzero
  rwa [jointDifference_apply,v0,sub_zero,←eval_mul] at nz

theorem marked_joint_residual_paid (ha:StrictLower A) (B:K[X]) {j:ℕ}
    (hp:(B*P).natDegree≤j) (pay:weightedEval (nodes A) v B∈defectPlus A 1 j) :
    contrastResidual A v P B∈defectPlus A 1 (j+1) := by
  rw [contrastResidual_apply,map_sub,show evalNodes A (primitive (B*P))-
    (mat A (evalNodes A (B*P))-mat A (weightedEval (nodes A) v B))=
      -(mat A (evalNodes A (B*P))-evalNodes A (primitive (B*P)))+
        mat A (weightedEval (nodes A) v B) by abel]
  exact Submodule.add_mem _
    (Submodule.neg_mem _ ((show zeroSpace A (j+1)≤defectPlus A 1 (j+1) from le_sup_left) (primitive_defect A _ hp)))
    (Fplus_mat ha 1 j ⟨_,pay,rfl⟩)

theorem FirstMarkedJoint.integral {B H:K[X]} {i:Fin (s+1)} {n:ℕ}
    (ha:StrictLower A) (D:FirstMarkedJoint A v U P B i) (C:Chart13 A 1 a r U w G)
    (hv:U.map (diag v)≤U) (fit:v*w-weightedEval (nodes A) w P∈U)
    (cap:defectPlus A 1 6≤chain (diag (nodes A)) U w n)
    (res:contrastResidual A v P B-evalNodes A H∈chain (diag (nodes A)) U w n) :
    (primitive (B*P)).eval (nodes A i)=H.eval (nodes A i) := by
  obtain ⟨p,hp,earlier⟩:=D.earlier
  have ap:mat A p∈defectPlus A 1 6 := Fplus_mat ha 1 5 ⟨_,C.marked.core hp,rfl⟩
  let z:=contrastResidual A v P B-evalNodes A H+mat A p
  have zz:z∈chain (diag (nodes A)) U w n := Submodule.add_mem _ res (cap ap)
  have e:=D.const_zero C hv fit zz ((primitive (B*P)).eval (nodes A i)-H.eval (nodes A i)) ?_
  · exact sub_eq_zero.mp e
  · intro j hj hc _
    have e : mat A (jointDifference A v P B) j=mat A p j :=
      strictlyCausal_mat ha j _ _ (fun k hk=>earlier k (lt_of_lt_of_le hk hj))
    dsimp only [z]
    rw [contrastResidual_apply]
    simp only [Pi.add_apply,Pi.sub_apply,evalNodes_apply]
    change (primitive (B*P)).eval (nodes A j)-mat A (jointDifference A v P B) j-
      H.eval (nodes A j)+mat A p j=_
    rw [e,hc]
    ring

omit [CharZero K] in
theorem marked_weight_from_grade (B:K[X]) {k:ℕ}
    (h:v∈defectPlus A 1 k) :
    weightedEval (nodes A) v B∈defectPlus A 1 (k+B.natDegree) := by
  apply weighted_paid
  intro m hm
  exact Fplus_mono A 1 (by have:=le_natDegree_of_mem_supp m hm;omega) (Fplus_power h m)

end RKCert.Paired.FiniteMidpoint
