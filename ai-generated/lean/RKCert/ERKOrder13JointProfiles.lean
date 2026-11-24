module
public import RKCert.ERKOrder13JointKnots
public import RKCert.ERKOrder13ThreeTwo
public import RKCert.GradeFiveSpace

@[expose] public section
/-! # Actual low-grade routes to the joint-block profile -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] {s r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w v:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 2600000

private theorem sq_mem_of_multiplier {v:Vec K (s+1)}
    (hv:U.map (diag v)≤U) (sq:v*v∈U) : v∈U := by
  classical
  rw [←sum_fibers v v]
  apply U.sum_mem
  intro z _
  by_cases ez:z=0
  · subst z
    have e : fiber v 0 v=0 := by
      ext i
      by_cases h:v i=0 <;> simp [fiber,h]
    rw [e]
    exact U.zero_mem
  · have e : fiber v z v=z⁻¹ • fiber v z (v*v) := by
      ext i
      by_cases h:v i=z
      · simp [fiber,h,←mul_assoc,inv_mul_cancel₀ ez]
      · simp [fiber,h]
    rw [e]
    exact U.smul_mem _ (fiber_mem hv z sq)

private theorem profile_from_head_square {c:Vec K (s+1)} {n:ℕ}
    (hv:U.map (diag v)≤U) (vn:v∉U) (head:v∈chain (diag c) U w 1)
    (sq:v*v∈chain (diag c) U w n) (nb:n≤4) :
    ∃ P:K[X], P≠0∧P.natDegree≤3∧v*w-weightedEval c w P∈U := by
  change v∈U⊔(K ∙ ((diag c)^0) w) at head
  simp only [pow_zero,one_apply_eq_self] at head
  obtain ⟨u,hu,z,hz,eq⟩:=Submodule.mem_sup.mp head
  obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hz
  have an:a≠0 := by
    intro ee
    apply vn
    rw [ee,zero_smul,add_zero] at eq
    rwa [←eq]
  obtain ⟨u',hu',Q,Qd,Qv⟩:=exists_head_poly sq
  let P:=a⁻¹ • Q
  have vu : v*u∈U := by
    have h:=hv ⟨u,hu,rfl⟩
    have ee : diag v u=v*u := by ext i;simp
    rwa [ee] at h
  have ee : v*w-weightedEval c w P=a⁻¹ • (u'-v*u) := by
    ext i
    have h:=Qv i
    change v i*v i=u' i+Q.eval (c i)*w i at h
    have e : v i=u i+a*w i := by
      have hp:=congrFun eq i
      simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] using hp.symm
    simp only [Pi.sub_apply,Pi.mul_apply,Pi.smul_apply,smul_eq_mul,weightedEval_apply,P,eval_smul]
    field_simp [an]
    linear_combination h-v i*e
  have fit :v*w-weightedEval c w P∈U := by
    rw [ee]
    exact U.smul_mem _ (U.sub_mem hu' vu)
  refine ⟨P,?_,?_,fit⟩
  · intro hz
    have e0 : weightedEval c w P=(0:Vec K (s+1)) := by rw [hz,map_zero]
    rw [e0,sub_zero] at fit
    apply vn (sq_mem_of_multiplier hv ?_)
    have exacts : v*v=v*u+a • (v*w) := by
      ext i
      have h:=congrFun eq i
      simp only [Pi.mul_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h ⊢
      linear_combination -(v i)*h
    rw [exacts]
    exact U.add_mem vu (U.smul_mem _ fit)
  · have h : Q.natDegree≤3 := by
      by_cases q0:Q=0
      · simp [q0]
      · have r := (natDegree_lt_iff_degree_lt q0).mpr Qd
        omega
    exact (natDegree_smul_le ..).trans h

private theorem profile_from_paid_shifts {c:Vec K (s+1)} {n j d:ℕ}
    (dis:∀ i,Live U i→w i=0) (count:n<(headSites c w).card) (budget:n≤d+4)
    (vn:v∉U) (paid:v∈chain (diag c) U w j)
    (band:∀ k≤d,(diag c^k) (v*w)∈chain (diag c) U w n) :
    ∃ P:K[X],P≠0∧P.natDegree≤3∧v*w-weightedEval c w P∈U := by
  classical
  obtain ⟨P,deg,rep⟩:=multiplier_degree dis count band
  have pn:P≠0 := by
    intro h
    apply vn
    obtain ⟨u,hu,R,_,eq⟩:=exists_head_poly paid
    have same : v=u := by
      ext i
      by_cases wz:w i=0
      · simpa only [wz,mul_zero,add_zero] using eq i
      · have uz:u i=0 := by by_contra hn;exact wz (dis i ⟨u,hu,hn⟩)
        rw [uz,rep i wz,h,eval_zero]
    rwa [same]
  refine ⟨P,pn,by have :=deg.resolve_left pn;omega,?_⟩
  have eq : v*w-weightedEval c w P=0 := by
    ext i
    by_cases wz:w i=0
    · simp [weightedEval_apply,wz]
    · simp [weightedEval_apply,rep i wz]
  rw [eq]
  exact U.zero_mem

theorem full13_actual_multiplier_stable [CharZero K] (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 r U w G)
    (v3:v∈zeroSpace A 3) : U.map (diag v)≤U := by
  rintro z ⟨u,hu,rfl⟩
  have eq : diag v u=u*v := by ext i;simp [mul_comm]
  rw [eq]
  exact full13_local_core_product ha ho S M C (j:=5) (k:=3)
    (fun _ hu=>tail_zero_iff.mp (C.marked.core hu)) (by decide) hu v3

theorem full13_clean_head_of_mul (C:Chart13 A 0 6 r U w G) (alg:MulClosed U)
    (act:∀u∈U,u*w∈U) : ∃ w':Vec K (s+1),Chart13 A 0 6 r U w' G ∧
      ∀i,Live U i→w' i=0 := by
  obtain ⟨v,_,dis,eq⟩:=disjoint_head C.marked.stable alg act
  have norm (z:K) (hz:fiber (nodes A) z v∈U) : fiber (nodes A) z v=0 := by
    classical
    ext i
    change fiber (nodes A) z v i=0
    by_contra hn
    have e:=dis i ⟨_,hz,hn⟩
    simp [fiber,e] at hn
  have H : MarkedHead A 6 0 r U v :=
    ⟨C.marked.rTwo,C.marked.rank,C.marked.core,C.marked.stable,norm,
      fun j hj hq=> (C.marked.paid j hj hq).trans (eq _).symm,
      C.marked.edge.trans (eq _).symm,C.marked.edgeRank⟩
  refine ⟨v,⟨H,C.shape,C.mesh,C.meshDegree,C.meshPaid,?_,C.rich⟩,dis⟩
  intro j hj hm
  unfold Band13 forwardBand
  rw [eq]
  exact C.chart j hj hm

private theorem no_quadratic_invariant_line [CharZero K] (ha:StrictLower A)
    (hS:Separated A 6) :
    ¬(mat A (qdef A)∈(K ∙ qdef A) ∧ diag (nodes A) (qdef A)∈(K ∙ qdef A)) := by
  rintro ⟨am,cd⟩
  let W : Submodule K (Vec K (s+1)) := K ∙ qdef A
  have put (N:Vec K (s+1)→ₗ[K] Vec K (s+1)) (hn:N (qdef A)∈W) :
      ∀v∈W,N v∈W := by
    intro v vv
    obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp vv
    rw [map_smul]
    exact W.smul_mem _ hn
  have seed : (2:K) • mat A (diag (nodes A) 1)-diag (nodes A) (diag (nodes A) 1)∈W := by
    rw [←qdef_seed]
    exact W.smul_mem _ (Submodule.mem_span_singleton_self _)
  have act:=mem_of_invariant_seed (Equiv.refl _) (mat A) (causal_mat ha) (nodes A) 1 W
    (put _ am) (put _ cd) seed
  have leF : W≤zeroSpace A 6 := (Submodule.span_singleton_le_iff_mem ..).mpr
    (zeroSpace_mono A (by decide) (qdef_mem A))
  have e : diag (nodes A) (1:Vec K (s+1))=nodes A := by ext i;simp
  rw [e] at act
  exact nodes_not_zeroSpace hS (by decide) (leF act)


section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

theorem order13_full_rank_three_three_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 3 U w G)
    (h4:finrank K (zeroSpace A 4)=3) : False := by
  let d:=qdef A
  let v:=mat A d
  let I:=U⊓zeroSpace A 3
  have U2 : finrank K U=2 := by have h:=C.marked.rank;omega
  have F3 := grade_three_eq_two_13 ha ho S h4
  have dn:d≠0:=qdef_ne_zero ha (S.separated.mono (by decide : 5≤6))
  have d2:d∈zeroSpace A 2:=qdef_mem A
  have dU:d∈U := by
    have h:=full13_lower_into_core S C.marked (k:=2) (by decide) (by decide) d2
    exact h
  have not_all : ¬zeroSpace A 3≤U := by
    intro e
    have N : zeroSpace A 3=U:=Submodule.eq_of_le_of_finrank_le e (by omega)
    have t := forward_invariant_hermite_rank ha ho (j:=3) (by decide) (zeroSpace A 3) le_rfl
      (fun x hx=>by
        have xu:x∈U:=N ▸ hx
        have yu:=C.marked.stable (Submodule.mem_map_of_mem (f:=diag (nodes A)) xu)
        simpa only [N] using yu)
    change finrank K (zeroSpace A 3)+2≤finrank K (zeroSpace A 4) at t
    omega
  have Ilt:I<zeroSpace A 3 := lt_of_le_of_ne inf_le_right (by
    intro e
    have inc:I≤U:=inf_le_left
    rw [e] at inc
    exact not_all inc)
  have Idim := Submodule.finrank_lt_finrank_of_lt Ilt
  have dI : d∈I := Submodule.mem_inf.mpr ⟨dU,zeroSpace_mono A (by decide) d2⟩
  have eqId : (K ∙ d)=I := by
    apply Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem ..).mpr dI)
    rw [finrank_span_singleton dn]
    omega
  have v3:v∈zeroSpace A 3 := mat_zeroSpace_charZero A 2 d2
  have vn:v∉U := by
    intro hv
    have vI : v∈I:=⟨hv,v3⟩
    have cI : diag (nodes A) d∈I := ⟨C.marked.stable ⟨d,dU,rfl⟩,diag_zeroSpace A 2 d2⟩
    rw [←eqId] at vI cI
    exact no_quadratic_invariant_line ha S.separated ⟨vI,cI⟩
  have hT : U.map (diag v)≤U := full13_actual_multiplier_stable ha ho S M C v3
  have head : v∈chain (diag (nodes A)) U w 1 :=
    full13_lower_into_core S C.marked (k:=3) (by decide) (by decide) v3
  have sq : v*v∈chain (diag (nodes A)) U w 4 := by
    have h := zeroSpace_mul (m:=3) (n:=3) v3 v3
    have h' := tail_zero_iff.mpr h
    rw [C.marked.paid 6 (by decide) le_rfl] at h'
    exact h'
  obtain ⟨P,pn,pd,fit⟩:=profile_from_head_square hT vn head sq (by decide)
  exact joint_thirteen_cubic_impossible ha ho S M C hT v3 pn pd fit

theorem order13_full_rank_four_outside_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 4 U w G)
    (outside:qdef A∉U) : False := by
  let d:=qdef A
  have d2:d∈zeroSpace A 2:=qdef_mem A
  have d3:d∈zeroSpace A 3:=zeroSpace_mono A (by decide) d2
  have hT : U.map (diag d)≤U := full13_actual_multiplier_stable ha ho S M C d3
  have head : d∈chain (diag (nodes A)) U w 1 :=
    full13_lower_into_core S C.marked (k:=2) (by decide) (by decide) d2
  have sq : d*d∈chain (diag (nodes A)) U w 3 :=
    full13_lower_into_core S C.marked (k:=4) (by decide) (by decide) (zeroSpace_mul (m:=2) (n:=2) d2 d2)
  obtain ⟨P,pn,pd,fit⟩:=profile_from_head_square hT outside head sq (by decide)
  exact joint_thirteen_cubic_impossible ha ho S M C hT d3 pn pd fit



omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem full13_power_five (C:Chart13 A 0 6 r U w G) {k:ℕ} (hk:k<r) :
    (diag (nodes A)^k) w∈zeroSpace A 5 := by
  apply tail_zero_iff.mp
  rw [C.marked.paid 5 le_rfl (by decide)]
  change ((diag (nodes A))^k) w∈chain (diag (nodes A)) U w r
  exact ((chain_le_iff _).mp le_rfl).2 k hk

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem shift_product13 (c:Vec K (s+1)) (v w:Vec K (s+1)) (k:ℕ) :
    (diag c^k) (v*w)=v*((diag c^k) w) := by
  ext i
  simp only [pow_diag_apply,Pi.mul_apply]
  ring

theorem order13_full_rank_four_inside_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 4 U w G)
    (inside:qdef A∈U) : False := by
  let d:=qdef A
  let v:=mat A d
  have dn:d≠0 := qdef_ne_zero ha (S.separated.mono (by decide : 5≤6))
  have d2:d∈zeroSpace A 2 := qdef_mem A
  have rU:finrank K U=1 := by have h:=C.marked.rank;omega
  have eqU:U=K∙d := by
    symm
    apply Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem ..).mpr inside)
    rw [finrank_span_singleton dn,rU]
  have payU:U≤zeroSpace A 2 := by rw [eqU];exact (Submodule.span_singleton_le_iff_mem ..).mpr d2
  have alg : MulClosed U := fun u hu z hz=> full13_local_core_product ha ho S M C (j:=2) (k:=2)
    payU (by decide) hu (payU hz)
  have act (u:Vec K (s+1)) (hu:u∈U) : u*w∈U := by
    apply full13_local_core_product ha ho S M C (j:=2) (k:=5) payU (by decide) hu
    simpa only [pow_zero,one_apply_eq_self] using full13_power_five C (k:=0) (by decide)
  obtain ⟨z,C,dis⟩:=full13_clean_head_of_mul C alg act
  have v3:v∈zeroSpace A 3 := mat_zeroSpace_charZero A 2 d2
  have vn:v∉U := by
    intro e
    have e' : diag (nodes A) d∈U := C.marked.stable (Submodule.mem_map_of_mem inside)
    rw [eqU] at e e'
    exact no_quadratic_invariant_line ha S.separated ⟨e,e'⟩
  have hV:=full13_actual_multiplier_stable ha ho S M C v3
  have base : v∈chain (diag (nodes A)) U z 2 :=
    full13_lower_into_core S C.marked (k:=3) (by decide) (by decide) v3
  let D:=diag (nodes A)
  have pay (k:ℕ) (hk:k≤3) : (D^k) (v*z)∈zeroSpace A 8 := by
    rw [shift_product13]
    exact zeroSpace_mul (m:=3) (n:=5) v3 (full13_power_five C (by omega))
  have band (k:ℕ) (hk:k≤3) : (D^k) (v*z)∈Band13 A 6 4 U z 8 := by
    have f (j:ℕ) : D ((D^j) (v*z))=(D^(j+1)) (v*z) := by simp only [pow_succ',mul_apply_eq_comp]
    by_cases less:k<3
    · exact (order13_full_no_leak ha ho S M C (pay k hk) (by rw [f];exact pay (k+1) (by omega))).1
    · have eq:k=2+1:=by omega
      rw [eq,←f]
      exact (order13_full_no_leak ha ho S M C (pay 2 (by decide)) (by rw [f];exact pay 3 (by decide))).2
  have cnt := band13_sites C
  change 9≤(headSites (nodes A) z).card at cnt
  obtain ⟨P,pn,pd,fit⟩:=profile_from_paid_shifts (d:=3) (n:=7) dis (by omega) (by decide) vn base band
  exact joint_thirteen_cubic_impossible ha ho S M C hV v3 pn pd fit

theorem order13_full_rank_five_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 5 U w G) : False := by
  let d:=qdef A
  have dn:d≠0 := qdef_ne_zero ha (S.separated.mono (by decide : 5≤6))
  have d2:d∈zeroSpace A 2 := qdef_mem A
  have d3:d∈zeroSpace A 3 := zeroSpace_mono A (by decide) d2
  have bot:U=⊥ := Submodule.finrank_eq_zero.mp (by have h:=C.marked.rank;omega)
  have vn:d∉U := by rw [bot,Submodule.mem_bot];exact dn
  have dis (i:Fin (s+1)) (hi:Live U i) : w i=0 := by
    obtain ⟨z,hz,hn⟩:=hi
    rw [bot,Submodule.mem_bot] at hz
    exact (hn (by rw [hz,Pi.zero_apply])).elim
  have base : d∈chain (diag (nodes A)) U w 2 :=
    full13_lower_into_core S C.marked (k:=2) (by decide) (by decide) d2
  have band (k:ℕ) (hk:k≤4) : (diag (nodes A)^k) (d*w)∈Band13 A 6 5 U w 7 := by
    rw [←order13_full_exact_F7 ha ho C,shift_product13]
    exact zeroSpace_mul (m:=2) (n:=5) d2 (full13_power_five C (by omega))
  have cnt := band13_sites C
  change 10≤(headSites (nodes A) w).card at cnt
  obtain ⟨P,pn,pd,fit⟩:=profile_from_paid_shifts (d:=4) (n:=7) dis (by omega) (by decide) vn base band
  exact joint_thirteen_cubic_impossible ha ho S M C
    (full13_actual_multiplier_stable ha ho S M C d3) d3 pn pd fit

end Ordered
end RKCert.Paired.FiniteMidpoint
