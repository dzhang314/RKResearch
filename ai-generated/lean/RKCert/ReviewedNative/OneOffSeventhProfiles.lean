module

public import RKCert.ReviewedNative.OneOffSeventhActions

@[expose] public section

/-! # Extract the actual quadratic defect coefficients from four clean rows -/
namespace RKResearch.Certified.Graded.OneOff.Seven
open RKResearch Polynomial Module
open scoped Classical Matrix

variable {K : Type*} [Field K] [CharZero K] {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12 → K}

noncomputable def qJPoly (d z : K) : K[X] :=
  let D := 12*z*(z-2*d)*paramT d
  monomial 0 (qJ0 d z/D)+monomial 1 (qJ1 d z/D)+monomial 2 (qJ2 d z/D)

noncomputable def qVPoly (d z : K) : K[X] :=
  C (4*d/5)*qJPoly d z-C (4*d/5)*((X:K[X])^2-C (2*d^2))

omit [CharZero K] in
theorem qJ_poly_eval (d z x : K) : (qJPoly d z).eval x=qJ d z x := by
  simp [qJPoly,qJ]
  ring

omit [CharZero K] in
theorem qV_poly_eval (d z x : K) : (qVPoly d z).eval x=qV d z x := by
  simp [qVPoly,qV,qJ_poly_eval]

omit [CharZero K] in
theorem qJ_poly_degree (d z : K) : (qJPoly d z).natDegree≤2 := by
  unfold qJPoly
  apply natDegree_add_le_of_le (m:=2) (n:=2)
  · apply natDegree_add_le_of_le (m:=2) (n:=2)
    · exact (natDegree_monomial_le _).trans (by decide)
    · exact (natDegree_monomial_le _).trans (by decide)
  · exact natDegree_monomial_le _

omit [CharZero K] in
theorem qV_poly_degree (d z : K) : (qVPoly d z).natDegree≤2 := by
  unfold qVPoly
  apply natDegree_sub_le_of_le (m:=2) (n:=2)
  · exact (natDegree_C_mul_le _ _).trans (qJ_poly_degree d z)
  · apply (natDegree_C_mul_le _ _).trans
    exact le_of_eq (natDegree_X_pow_sub_C (2*d^2))

structure CleanFour (A : Matrix (Fin 12) (Fin 12) K) (a d z : K) : Prop where
  node2 : nodes A (2:Fin 12)=d
  node3 : nodes A (3:Fin 12)=2*d
  node4 : nodes A (4:Fin 12)=2*d
  node5 : nodes A (5:Fin 12)=z
  g2 : g A (2:Fin 12)=0
  g3 : g A (3:Fin 12)=0
  g4 : g A (4:Fin 12)=0
  g5 : g A (5:Fin 12)=0
  H2 : scaledH A a (2:Fin 12)=hzero d d
  H5 : scaledH A a (5:Fin 12)=hzero d z
  diff : scaledH A a (4:Fin 12)≠scaledH A a (3:Fin 12)

theorem order9_clean_four (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 9 A b)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j) (F : FirstFour A a d (by decide)) :
    CleanFour A a d (nodes A (5:Fin 12)) := by
  let z := nodes A (5:Fin 12)
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have f2 : nodes A (2:Fin 12)=d ∧ g A (2:Fin 12)=0 ∧ h A (2:Fin 12)=twoHd a d := by
    simpa [chartNode,chartDefect,chartH] using F.features 2
  have f3 : nodes A (3:Fin 12)=2*d ∧ g A (3:Fin 12)=0 ∧ h A (3:Fin 12)=a*d^2 := by
    simpa [chartNode,chartDefect,chartH] using F.features 3
  have f4 := order9_fifth_feature ha ho D F
  have f5 := order9_sixth_feature ha ho D F
  refine ⟨f2.1,f3.1,f4.1,rfl,f2.2.1,f3.2.1,f4.2.1,f5.1,?_,?_,?_⟩
  · rw [scaledH_eval,f2.2.2,twoHd,hzero]
    field_simp [an,dn]
    ring
  · rw [scaledH_eval,f5.2.2.2.2.1,hzero]
    field_simp [an,dn]
  · intro e
    rw [scaledH_eval,scaledH_eval,f3.2.2] at e
    exact f4.2.2 ((div_left_inj₀ an).mp e)

theorem hzero_at_d (d : K) (dn : d≠0) : hzero d d= -d^2/4 := by
  unfold hzero
  field_simp [dn]
  ring

theorem hzero_ne (d z : K) (dn : d≠0) (zn : z≠0) (zt : z≠2*d) :
    hzero d z≠0 := by
  unfold hzero
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 zn) (sub_ne_zero.mpr zt))
    (mul_ne_zero (by norm_num) dn)

/-- Every grade-five defect has a radial polynomial part. Two points
on the repeated clock fix its factor, and three distinct nonzero Ag
columns fix its remaining quadratic on every on row. -/
theorem native_defect_profile (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 9 A b)
    {a d z : K} (an : a≠0) (dn : d≠0) (zn : z≠0) (zd : z≠d) (zt : z≠2*d)
    (C4 : CleanFour A a d z) (rt : radauVal (2*d)≠0)
    (mEq : LinearMap.range (normalProfileMap A)=treeSpace A 5)
    {v : Fin 12 → K} (vm : v∈zeroSpace A 5) (k : K) (Q : K[X]) (qDeg : Q.natDegree≤2)
    (r2 : v (2:Fin 12)=k*radauVal d+scaledH A a (2:Fin 12)*Q.eval d)
    (r3 : v (3:Fin 12)=k*radauVal (2*d)+scaledH A a (3:Fin 12)*Q.eval (2*d))
    (r4 : v (4:Fin 12)=k*radauVal (2*d)+scaledH A a (4:Fin 12)*Q.eval (2*d))
    (r5 : v (5:Fin 12)=k*radauVal z+scaledH A a (5:Fin 12)*Q.eval z) :
    ∀ r, g A r=0 → v r=k*radauVal (nodes A r)+scaledH A a r*Q.eval (nodes A r) := by
  have vv : v∈LinearMap.range (normalProfileMap A) := by
    rw [mEq]; exact zeroSpace_le_treeSpace A 5 vm
  obtain ⟨w,hw⟩ := vv
  have dvm : normalProfileMap A w∈zeroSpace A 5 := hw ▸ vm
  have pfit := normal_profile_defect_poly ha ho w dvm
  let R := C a * ofFn 3 w.2.2
  have act (r : Fin 12) (gr : g A r=0) :
      v r=w.1 5*radauVal (nodes A r)+scaledH A a r*R.eval (nodes A r) := by
    rw [←hw,normal_profile_value,gr,mul_zero,zero_add,pfit,eval_mul,eval_C,←radauVal_eq,
      scaledH_eval]
    simp only [R,eval_mul,eval_C]
    field_simp [an]
  have e3 := r3.symm.trans (show v (3:Fin 12)=w.1 5*radauVal (2*d)+
      scaledH A a (3:Fin 12)*R.eval (2*d) by
        simpa only [C4.node3] using act (3:Fin 12) C4.g3)
  have e4 := r4.symm.trans (show v (4:Fin 12)=w.1 5*radauVal (2*d)+
      scaledH A a (4:Fin 12)*R.eval (2*d) by
        simpa only [C4.node4] using act (4:Fin 12) C4.g4)
  obtain ⟨ek,eT⟩ := common_clock_affine_parameters C4.diff e3 e4
  have kk := mul_right_cancel₀ rt ek
  have dneq : scaledH A a (2:Fin 12)≠0 := by
    rw [C4.H2,hzero_at_d d dn]
    exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 dn)) (by norm_num)
  have zneq : scaledH A a (5:Fin 12)≠0 := by
    rw [C4.H5]
    exact hzero_ne d z dn zn zt
  have eD : R.eval d=Q.eval d := by
    have e := act (2:Fin 12) C4.g2
    rw [C4.node2,kk] at e
    exact mul_left_cancel₀ dneq (add_left_cancel (e.symm.trans r2))
  have eZ : R.eval z=Q.eval z := by
    have e := act (5:Fin 12) C4.g5
    rw [C4.node5,kk] at e
    exact mul_left_cancel₀ zneq (add_left_cancel (e.symm.trans r5))
  have dt : d≠2*d := by intro v; exact dn (by linear_combination -v)
  have SS : ({d,2*d,z}:Finset K).card=3 := by simp [dt,Ne.symm zd,Ne.symm zt]
  have rd : R.natDegree≤2 := (natDegree_C_mul_le _ _).trans
    (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _))
  have dd := natDegree_sub_le_of_le rd qDeg
  have zero : R-Q=0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (R-Q)
    ({d,2*d,z}:Finset K) (fun x hx=>by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl|rfl <;> simp [eD,eT,eZ]) (by rw [SS]; simpa using Nat.lt_succ_of_le dd)
  have Qeq := sub_eq_zero.mp zero
  intro r gr
  simpa only [kk,Qeq] using act r gr

theorem native_jv_profiles (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 9 A b)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j) (F : FirstFour A a d (by decide)) :
    let z := nodes A (5:Fin 12)
    ∀ r, g A r=0 →
      Jtest A a r=jRadau d*radauVal (nodes A r)+scaledH A a r*qJ d z (nodes A r) ∧
      Vtest A a r=((4*d/5)*jRadau d)*radauVal (nodes A r)+scaledH A a r*qV d z (nodes A r) := by
  let z := nodes A (5:Fin 12)
  have dn := D.base.dn
  have C4 := order9_clean_four ha ho D F
  obtain ⟨rk,mEq,Rt,_⟩ := order9_maximal_normal_profile ha ho D F
  rw [←radauVal_eq] at Rt
  have sixth := order9_sixth_feature ha ho D F
  have zn : z≠0 := sixth.2.1
  have zd : z≠d := sixth.2.2.1
  have zt : z≠2*d := sixth.2.2.2.1
  have tn : paramT d≠0 := by
    intro tt
    exact Rt (by rw [radauVal_doubled,tt,mul_zero,zero_div])
  have acts (r : Fin 12) (rr : r.val≤5) (gr : g A r=0) :
      Jtest A a r=jValue d z (nodes A r) (scaledH A a r) ∧
      Vtest A a r=vValue d z (nodes A r) (scaledH A a r) :=
    order9_actions_seven ha D gr
      (fun l lr=>order9_native_sources ha ho D F l
        (by have h : l.val<r.val := lr; omega))
  have nn (r : Fin 12) (rr : r.val≤5) (gr : g A r=0)
      (jj : jResidual d z (nodes A r) (scaledH A a r)=0)
      (master : (nodes A r-2*d)*(nodes A r-z)*
        (4*d*scaledH A a r-(nodes A r)^2*(nodes A r-2*d))=0) :
      Jtest A a r=jRadau d*radauVal (nodes A r)+scaledH A a r*(qJPoly d z).eval (nodes A r) ∧
      Vtest A a r=((4*d/5)*jRadau d)*radauVal (nodes A r)+scaledH A a r*(qVPoly d z).eval (nodes A r) := by
    have eq := master_residual d z (nodes A r) (scaledH A a r) dn
    have aa := acts r rr gr
    rw [jj,mul_zero,sub_zero,master,zero_div] at eq
    unfold jResidual at jj
    unfold vResidual at eq
    rw [qJ_poly_eval,qV_poly_eval,aa.1,aa.2]
    exact ⟨by linear_combination jj,by linear_combination eq⟩
  have n2 := nn (2:Fin 12) (by decide) C4.g2 (by
    rw [C4.node2,C4.H2]; exact j_at_d d z dn zn zt tn) (by
    rw [C4.node2,C4.H2,hzero]
    field_simp [dn]
    ring)
  have n3 := nn (3:Fin 12) (by decide) C4.g3 (by
    rw [C4.node3]; exact j_at_t d z _ dn zn zt tn) (by simp [C4.node3])
  have n4 := nn (4:Fin 12) (by decide) C4.g4 (by
    rw [C4.node4]; exact j_at_t d z _ dn zn zt tn) (by simp [C4.node4])
  have n5 := nn (5:Fin 12) (by decide) C4.g5 (by
    rw [C4.node5,C4.H5]; exact j_at_z d z dn zn zt tn) (by simp [z])
  rw [C4.node2] at n2
  rw [C4.node3] at n3
  rw [C4.node4] at n4
  rw [C4.node5] at n5
  have J := native_defect_profile ha ho D.base.origin.a_ne dn zn zd zt C4 Rt mEq
    (Jtest_mem ho a) (jRadau d) (qJPoly d z) (qJ_poly_degree d z) n2.1 n3.1 n4.1 n5.1
  have V := native_defect_profile ha ho D.base.origin.a_ne dn zn zd zt C4 Rt mEq
    (Vtest_mem A a) ((4*d/5)*jRadau d) (qVPoly d z) (qV_poly_degree d z) n2.2 n3.2 n4.2 n5.2
  dsimp only
  intro r rg
  simpa only [qJ_poly_eval,qV_poly_eval] using And.intro (J r rg) (V r rg)

end RKResearch.Certified.Graded.OneOff.Seven
