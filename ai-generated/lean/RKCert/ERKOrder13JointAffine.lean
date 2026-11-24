module
public import RKCert.ERKOrder13MarkedJoint

@[expose] public section
/-! # Affine-head product and literal factor from joint blocks
A block whose multiplier value disagrees with P is absorbed into the
invariant core. In a surviving block, both the affine multiplier and
the mesh are constant modulo the one scalar head component. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Paired.OrderTwelve
  RKCert.Endpoint Module Polynomial
variable {K:Type*} [Field K] [CharZero K] {s a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w v:Vec K (s+1)} {G P:K[X]}
set_option maxHeartbeats 3900000

theorem marked13_multiplier_stable (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G)
    (v3:v∈defectPlus A 1 3) : U.map (diag v)≤U := by
  rintro z ⟨u,hu,rfl⟩
  have eq : diag v u=u*v := by ext i;simp [mul_comm]
  rw [eq]
  exact marked13_local_core_product ha ho S M C (j:=5) (k:=3)
    C.marked.core (by decide) hu v3

omit [CharZero K] in
private theorem square_absorbs {v:Vec K (s+1)} (hv:U.map (diag v)≤U)
    (hm:v*v∈U) : v∈U := by
  classical
  rw [←sum_fibers v v]
  apply U.sum_mem
  intro z _
  by_cases hz:z=0
  · subst z
    have zero:fiber v 0 v=0 := by
      ext i
      by_cases hi:v i=0 <;> simp [fiber,hi]
    rw [zero]
    exact U.zero_mem
  · have e:fiber v z v=z⁻¹•fiber v z (v*v) := by
      ext i
      by_cases hi:v i=z <;> simp [fiber,hi,←mul_assoc,inv_mul_cancel₀ hz]
    rw [e]
    exact U.smul_mem _ (fiber_mem hv _ hm)

omit [CharZero K] in
theorem affine_profile_of_square {c:Vec K (s+1)} {n:ℕ} (npos:0<n)
    (stable:U.map (diag v)≤U) (vn:v∉U)
    (head:v∈chain (diag c) U w 1) (sq:v*v∈chain (diag c) U w n) :
    ∃ α:K,∃ u:Vec K (s+1),∃ P:K[X], α≠0 ∧ u∈U ∧ v=u+α•w ∧
      P≠0 ∧ P.natDegree<n ∧ v*w-weightedEval c w P∈U := by
  change v∈U⊔(K ∙ ((diag c)^0) w) at head
  simp only [pow_zero,one_apply_eq_self] at head
  obtain ⟨u,hu,z,hz,e⟩:=Submodule.mem_sup.mp head
  obtain ⟨α,rfl⟩:=Submodule.mem_span_singleton.mp hz
  have an:α≠0 := by
    intro z
    apply vn
    rw [z,zero_smul,add_zero] at e
    rwa [←e]
  obtain ⟨k,hk,Q,Qd,qq⟩:=exists_head_poly sq
  let P:=α⁻¹•Q
  have vu : v*u∈U := by
    have h:=stable ⟨u,hu,rfl⟩
    have ee : diag v u=v*u := by ext i;simp
    rwa [ee] at h
  have ve:v*v=v*u+α•(v*w) := by
    ext i
    have h:=congrFun e i
    simp only [Pi.mul_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h ⊢
    linear_combination -(v i)*h
  have eq : v*w-weightedEval c w P=α⁻¹•(k-v*u) := by
    ext i
    have h:=qq i
    change v i*v i=k i+Q.eval (c i)*w i at h
    have a:=congrFun ve i
    simp only [Pi.sub_apply,Pi.mul_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,weightedEval_apply,
      P,eval_smul] at a ⊢
    field_simp [an]
    linear_combination h-a
  have fit:v*w-weightedEval c w P∈U := by
    rw [eq]
    exact U.smul_mem _ (U.sub_mem hk vu)
  have pn:P≠0 := by
    intro p0
    rw [p0,map_zero,sub_zero] at fit
    apply vn (square_absorbs stable ?_)
    rw [ve]
    exact U.add_mem vu (U.smul_mem _ fit)
  have qd:Q.natDegree<n := by
    by_cases q0:Q=0
    · simpa only [q0,natDegree_zero] using npos
    · exact (natDegree_lt_iff_degree_lt q0).mpr Qd
  exact ⟨α,u,P,an,hu,e.symm,pn,(natDegree_smul_le _ _).trans_lt qd,fit⟩

omit [CharZero K] in
theorem marked13_affine_literal (C:Chart13 A 1 a r U w G) (hr:3≤r)
    (hs:U.map (diag v)≤U)
    (α:K) (an:α≠0) (u:Vec K (s+1)) (hu:u∈U) (aff:v=u+α•w)
    (pn:P≠0) (pd:P.natDegree≤3)
    (mult:v*w-weightedEval (nodes A) w P∈U) :
    ∃ Q:K[X],Q.natDegree≤r+1 ∧ α•G=P*Q := by
  classical
  let c:=nodes A
  have edge:=C.meshPaid
  rw [C.marked.edge] at edge
  obtain ⟨g,hg,Q,Qd,mes⟩:=exists_head_poly edge
  have qd:Q.natDegree≤r+1 := by
    by_cases h:Q=0
    · simp [h]
    · have d:Q.natDegree<r+(6-4) := (natDegree_lt_iff_degree_lt h).mpr Qd
      omega
  have N:=band13_sites C
  have width:=C.width
  have tw:=C.marked.rTwo
  have value (x:K) (hx:x∈headSites c w) : α*G.eval x=P.eval x*Q.eval x := by
    obtain ⟨i,wi,ix⟩:=stage_of_headSite13 hx
    let E:=fiber c x w
    have Ee:E≠0 := by
      intro z
      have t:=congrFun z i
      have e : c i=x := ix
      simp only [E,fiber,e,ite_true,Pi.zero_apply] at t
      exact wi t
    have En:E∉U := fun h=>Ee (C.marked.norm x h)
    let Z:=fiber v (P.eval x) E
    have Zn:Z∉U := by
      intro h
      apply En
      rw [←sum_fibers v E]
      apply U.sum_mem
      intro z _
      by_cases zz:z=P.eval x
      · subst z;exact h
      · exact profile_vanish_on_block C.marked.stable hs mult zz
    let I:=fiber v (P.eval x) (fiber c x (1:Vec K (s+1)))
    let S:=fiber v (P.eval x) (fiber c x u)
    let T:=fiber v (P.eval x) (fiber c x g)
    have Sm:S∈U := fiber_mem hs _ (fiber_mem C.marked.stable _ hu)
    have Tm:T∈U := fiber_mem hs _ (fiber_mem C.marked.stable _ hg)
    have a1:P.eval x•I=S+α•Z := by
      ext j
      by_cases hc:c j=x <;> by_cases hv:v j=P.eval x
      · have e:=congrFun aff j
        simpa only [I,S,Z,E,fiber,hc,hv,ite_true,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
          Pi.one_apply,mul_one] using e
      all_goals simp [I,S,Z,E,fiber,hc,hv]
    have a2:G.eval x•I=T+Q.eval x•Z := by
      ext j
      by_cases hc:c j=x <;> by_cases hv:v j=P.eval x
      · have e:=mes j
        have zc:nodes A j=x := hc
        simpa only [I,T,Z,E,fiber,hc,zc,hv,ite_true,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
          Pi.one_apply,mul_one,evalNodes_apply] using e
      all_goals simp [I,T,Z,E,fiber,hc,hv]
    have In:I∉U := by
      intro z
      have az:α•Z∈U := by
        have e := U.sub_mem (U.smul_mem (P.eval x) z) Sm
        rw [a1,add_sub_cancel_left] at e
        exact e
      exact Zn ((U.smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr an)).mp az)
    have finish : (α*G.eval x-P.eval x*Q.eval x)•I=α•T-Q.eval x•S := by
      ext j
      have O:=congrFun a1 j
      have D:=congrFun a2 j
      simp only [Pi.smul_apply,smul_eq_mul,Pi.add_apply,Pi.sub_apply] at O D ⊢
      linear_combination α*D-Q.eval x*O
    by_contra hn
    have ne := sub_ne_zero.mpr hn
    apply In
    apply (U.smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr ne)).mp
    rw [finish]
    exact U.sub_mem (U.smul_mem _ Tm) (U.smul_mem _ Sm)
  refine ⟨Q,qd,?_⟩
  apply eq_of_degrees_lt_of_eval_finset_eq (headSites c w)
  · have h := (natDegree_smul_le α G).trans_eq C.meshDegree
    exact degree_le_natDegree.trans_lt (by exact_mod_cast (show (α•G).natDegree < (headSites c w).card by
      change headLen 6 a r 10≤(headSites c w).card at N
      unfold headLen at N
      omega))
  · have h := natDegree_mul_le (p:=P) (q:=Q)
    exact degree_le_natDegree.trans_lt (by exact_mod_cast (show (P*Q).natDegree < (headSites c w).card by
      change headLen 6 a r 10≤(headSites c w).card at N
      unfold headLen at N
      omega))
  · intro x hx
    simpa only [eval_smul,smul_eq_mul,eval_mul] using value x hx

end RKCert.Paired.FiniteMidpoint
