module

public import RKCert.ReviewedNative.OneOffSeventhEndpoint

@[expose] public section

/-! # The seventh real row must be a new Ag value at the sixth clock -/
namespace RKResearch.Certified.Graded.OneOff.Seven
open RKResearch Polynomial Module
open RKCert.Paired.OneOff (endpointF endpointG endpoint_nonzero readGrid endpointFData endpointG_formula)
open scoped Classical Matrix

variable {K : Type*} [Field K] [CharZero K] {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12 → K}

omit [CharZero K] in
theorem no_further_on_same_clock (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 9 A b)
    (rk : finrank K (treeSpace A 5)=10) (mEq : LinearMap.range (normalProfileMap A)=treeSpace A 5)
    {l m r : Fin 12} (pre : IndependentBefore (treeSpace A 4) r) (lr : l < r) (mr : m < r)
    (lc : nodes A l=nodes A r) (mc : nodes A m=nodes A r)
    (lg : g A l=0) (mg : g A m=0) (rg : g A r=0) (dh : h A m≠h A l) : False := by
  let α := (h A r-h A l)/(h A m-h A l)
  apply order9_no_interpolated_feature ha ho rk mEq pre lr mr lc mc α
  · rw [rg,lg,mg]; ring
  · dsimp only [α]
    field_simp [sub_ne_zero.mpr dh]
    ring

theorem off_repeats_first (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 9 A b)
    {a d : K} {i j r : Fin 12} (D : GlobalNormal A a d i j) (F : FirstFour A a d (by decide))
    (rk : finrank K (treeSpace A 5)=10) (mEq : LinearMap.range (normalProfileMap A)=treeSpace A 5)
    (pre : IndependentBefore (treeSpace A 4) r) (r1 : (1:Fin 12)<r) (off : g A r≠0) : False := by
  have f1 : nodes A (1:Fin 12)=a ∧ g A (1:Fin 12)=baseAmp a ∧ h A (1:Fin 12)=0 := by
    simpa [chartNode,chartDefect,chartH] using F.features 1
  have w := congrFun (order9_defects_separate ha ho D) r
  change g A r*h A r=0 at w
  exact order9_no_repeated_feature ha ho rk mEq pre r1
    (f1.1.trans (D.base.origin.off_support r off).symm)
    (f1.2.1.trans (amplitude_value D.base.amplitude off).symm)
    (f1.2.2.trans ((mul_eq_zero.mp w).resolve_left off).symm)

structure TwoFibres (A : Matrix (Fin 12) (Fin 12) K) (a d z : K) : Prop where
  endpoint : EndpointChart A a d z
  node7 : nodes A (6:Fin 12)=z
  g7 : g A (6:Fin 12)=0
  Hdiff : scaledH A a (6:Fin 12)≠scaledH A a (5:Fin 12)
  pz : endP d z=0
  qz : (terminalQ d z).eval z=0
  q_nonzero : terminalQ d z≠0
  pd : endP d d≠0
  z1 : z≠1

set_option maxHeartbeats 2100000 in
theorem order9_two_fibres (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 9 A b)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j) (F : FirstFour A a d (by decide)) :
    TwoFibres A a d (nodes A (5:Fin 12)) := by
  let r : Fin 12 := 6
  let x := nodes A r
  let z := nodes A (5:Fin 12)
  let H := scaledH A a r
  let Q := terminalQ d z
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have C4 := order9_clean_four ha ho D F
  have E := order9_actual_endpoint_chart ha ho D F
  have un := E.Un
  obtain ⟨rk,mEq,Rt,t1⟩ := order9_maximal_normal_profile ha ho D F
  have tn : paramT d≠0 := by
    intro tt
    exact Rt (by rw [←radauVal_eq,radauVal_doubled,tt,mul_zero,zero_div])
  have sixth := order9_sixth_feature ha ho D F
  have zn : z≠0 := sixth.2.1
  have zd : z≠d := sixth.2.2.1
  have zt : z≠2*d := sixth.2.2.2.1
  have ind : IndependentBefore (treeSpace A 4) r := sixth.2.2.2.2.2
  have g0 : g A r=0 := by
    by_contra nog
    exact off_repeats_first ha ho D F rk mEq ind (by decide) nog
  have nt : x≠2*d := by
    intro same
    have hh : h A (4:Fin 12)≠h A (3:Fin 12) := fun h => C4.diff (by rw [scaledH_eval,scaledH_eval,h])
    exact no_further_on_same_clock ha ho rk mEq ind
      (show (3:Fin 12)<r by decide) (show (4:Fin 12)<r by decide)
      (C4.node3.trans same.symm) (C4.node4.trans same.symm) C4.g3 C4.g4 g0 hh
  have act := order9_actions_seven ha D (z:=z) g0
    (fun l ll=>order9_native_sources ha ho D F l ll)
  have pr := native_jv_profiles ha ho D F r g0
  have jr : jResidual d z x H=0 := by
    unfold jResidual
    have e := act.1.symm.trans pr.1
    dsimp only [x,H] 
    linear_combination e
  have vr : vResidual d z x H=0 := by
    unfold vResidual
    have e := act.2.symm.trans pr.2
    dsimp only [x,H]
    linear_combination e
  have er : endP d x+Q.eval x*H=0 := E.eq_on r (by decide) g0
  have xz : x=z := by
    by_contra nz
    have MM := master_residual d z x H dn
    rw [jr,vr,mul_zero,sub_zero,eq_comm,div_eq_zero_iff] at MM
    have mul0 : (x-2*d)*(x-z)*(4*d*H-x^2*(x-2*d))=0 :=
      MM.resolve_right (by norm_num : (5:K)≠0)
    have hz := sub_eq_zero.mp ((mul_eq_zero.mp mul0).resolve_left
      (mul_ne_zero (sub_ne_zero.mpr nt) (sub_ne_zero.mpr nz)))
    have hf : H=hzero d x := by
      unfold hzero
      apply (eq_div_iff (mul_ne_zero (by norm_num : (4:K)≠0) dn)).mpr
      linear_combination hz
    have x0 : x≠0 := by
      intro x0
      have f : nodes A (0:Fin 12)=0 ∧ g A (0:Fin 12)=0 ∧ h A (0:Fin 12)=0 := by
        simpa [chartNode,chartDefect,chartH] using F.features 0
      have h0 : h A r=0 := by
        rw [x0] at hf
        simp only [hzero,zero_pow (by decide : (2:ℕ)≠0),zero_mul,zero_div,H,scaledH_eval] at hf
        exact (div_eq_zero_iff.mp hf).resolve_right an
      exact order9_no_repeated_feature ha ho rk mEq ind (show (0:Fin 12)<r by decide)
        (f.1.trans x0.symm) (f.2.1.trans g0.symm) (f.2.2.trans h0.symm)
    have xd : x≠d := by
      intro xD
      have hp : scaledH A a (2:Fin 12)=scaledH A a r := by
        rw [C4.H2]
        exact (congrArg (hzero d) xD.symm).trans hf.symm
      rw [scaledH_eval,scaledH_eval] at hp
      exact order9_no_repeated_feature ha ho rk mEq ind (show (2:Fin 12)<r by decide)
        (C4.node2.trans xD.symm) (C4.g2.trans g0.symm) ((div_left_inj₀ an).mp hp)
    have prefixNZ := mul_ne_zero (mul_ne_zero (mul_ne_zero x0 (sub_ne_zero.mpr nt))
      (sub_ne_zero.mpr xd)) (sub_ne_zero.mpr nz)
    have rowJ := cubic_j_residual d z x dn zn zt tn
    rw [←hf,jr] at rowJ
    have k0 : mixedK d z x=0 := by
      by_contra kn
      apply div_ne_zero ?_ (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (12:K)≠0) zn)
        (sub_ne_zero.mpr zt)) tn) rowJ.symm
      simpa only [mul_assoc] using mul_ne_zero
        (mul_ne_zero (by norm_num : (5:K)≠0) dn) (mul_ne_zero prefixNZ kn)
    change endP d x+(terminalQ d z).eval x*H=0 at er
    rw [terminalQ_eval,hf] at er
    have ej := cubic_endpoint_residual d z x dn zn zd zt t1 un
    rw [er,k0,mul_zero,zero_sub] at ej
    exact div_ne_zero
      (mul_ne_zero prefixNZ (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero un tn) x0) zn)))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (by norm_num : (2:K)≠0) (pow_ne_zero 2 dn)) zn) (sub_ne_zero.mpr zt))
          (sub_ne_zero.mpr t1)) un) ej.symm
  have hdif : H≠scaledH A a (5:Fin 12) := by
    intro eq
    change scaledH A a r=_ at eq
    rw [scaledH_eval,scaledH_eval] at eq
    exact order9_no_repeated_feature ha ho rk mEq ind (show (5:Fin 12)<r by decide)
      (C4.node5.trans xz.symm) (C4.g5.trans g0.symm) (((div_left_inj₀ an).mp eq).symm)
  have e5 := E.eq_on (5:Fin 12) (by decide) C4.g5
  rw [C4.node5] at e5
  rw [xz] at er
  have qz : Q.eval z=0 := (mul_eq_zero.mp
    (show Q.eval z*(H-scaledH A a (5:Fin 12))=0 by linear_combination er-e5)).resolve_right
      (sub_ne_zero.mpr hdif)
  have pz : endP d z=0 := by rwa [qz,zero_mul,add_zero] at er
  have z1 : z≠1 := fun e=>one_ne_zero (E.p1.symm.trans (e ▸ pz))
  have slope := j_slope_at_z d z (scaledH A a (5:Fin 12)) H dn zn zt tn
  rw [xz] at jr
  rw [jr,C4.H5,j_at_z d z dn zn zt tn,sub_self] at slope
  -- Restore the exact nonzero coordinate difference after the simplifier.
  have hdif' : H≠hzero d z := fun eq=>hdif (eq.trans C4.H5.symm)
  have Gn : endpointG d z=0 := by
    by_contra nz
    exact mul_ne_zero
      (div_ne_zero (mul_ne_zero (by norm_num : (-5:K)≠0) nz)
        (mul_ne_zero (mul_ne_zero (by norm_num : (12:K)≠0) zn) tn))
      (sub_ne_zero.mpr hdif') slope.symm
  have denom : 2*(1-2*d)*paramU d≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (Ne.symm t1))) un
  have Fz : endpointF d z=0 := by
    by_contra nz
    exact div_ne_zero (mul_ne_zero (mul_ne_zero zn (sub_ne_zero.mpr zt)) nz) denom pz
  have qn : Q≠0 := by
    intro q0
    have e := E.eq_on (2:Fin 12) (by decide) C4.g2
    change endP d (nodes A (2:Fin 12))+Q.eval (nodes A (2:Fin 12))*scaledH A a (2:Fin 12)=0 at e
    rw [C4.node2,q0,eval_zero,zero_mul,add_zero] at e
    have Fd : endpointF d d=0 := by
      by_contra n
      exact div_ne_zero (mul_ne_zero (mul_ne_zero dn
        (sub_ne_zero.mpr (show d≠2*d by intro h; exact dn (by linear_combination -h)))) n) denom e
    exact endpoint_nonzero zd Fd Fz Gn
  have pd : endP d d≠0 := by
    intro p0
    have e := E.eq_on (2:Fin 12) (by decide) C4.g2
    rw [C4.node2,p0,zero_add,C4.H2] at e
    have qd := (mul_eq_zero.mp e).resolve_right
      (hzero_ne d d dn dn (by intro h; exact dn (by linear_combination -h)))
    have dt : d≠2*d := by intro h; exact dn (by linear_combination -h)
    have S : ({d,2*d,z}:Finset K).card=3 := by simp [dt,Ne.symm zd,Ne.symm zt]
    exact qn (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      Q ({d,2*d,z}:Finset K) (fun x hx=>by
        simp only [Finset.mem_insert,Finset.mem_singleton] at hx
        rcases hx with rfl|rfl|rfl
        · exact qd
        · simp [Q,terminalQ_eval]
        · exact qz) (by rw [S]; exact Nat.lt_succ_of_le (terminalQ_degree d z)))
  exact ⟨E,xz,g0,hdif,pz,qz,qn,pd,z1⟩


/-- The actual seventh physical row closes the second fibre, with its
cubic/quartic terminal profile paid by native reviewed order. -/
theorem order9_one_off_two_fibres (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 9 A b) (off : (offKnots A).card = 1) :
    ∃ (a d : K) (i j : Fin 12), GlobalNormal A a d i j ∧ FirstFour A a d (by decide) ∧
      TwoFibres A a d (nodes A (5:Fin 12)) := by
  obtain ⟨a,d,i,j,D,F⟩ := order9_first_four ha ho off
  exact ⟨a,d,i,j,D,F,order9_two_fibres ha ho D F⟩

end RKResearch.Certified.Graded.OneOff.Seven
