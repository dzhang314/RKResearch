module
public import RKCert.ReviewedNative.ERK8PaidArithmetic

public import RKCert.ReviewedNative.ERK8PaidOneOffTerminal

@[expose] public section

/-! Physical seventh-row contradiction from the real p8 profiles.
This is a source candidate, not a replay result. -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof.Eight

open RKResearch Polynomial Module Reverse
open scoped Matrix Classical

variable {K : Type*} [Field K] [EightUnits K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

theorem d_ne_double {d : K} (dn : d≠0) : d≠2*d := by
  intro e
  exact dn (by linear_combination (norm := eight_ring K) -e)

theorem height_identity (d x : K) (dn : d≠0) :
    4*d*hzero d x=x^2*(x-2*d) := by
  unfold hzero
  field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,dn] <;> eight_ring K

theorem height_ne (d x : K) (dn : d≠0) (xn : x≠0) (xD : x≠2*d) :
    hzero d x≠0 := by
  unfold hzero
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 xn) (sub_ne_zero.mpr xD))
    (mul_ne_zero (by eight_num) dn)

theorem scaledAtTwo {a d : K} {i j : Fin 10} (D : GlobalNormal A a d i j)
    (R : PhysicalPrefix A a d) : scaled A a (2:Fin 10)=hzero d d := by
  have e : h A (2:Fin 10)=twoHd a d := by
    simpa [chartH] using (R.first.features 2).2.2
  rw [scaled_eval,e,twoHd,hzero]
  field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,D.base.origin.a_ne,D.base.dn] <;> eight_ring K

theorem scaledAtFive {a d : K} (an : a≠0) (R : PhysicalPrefix A a d) :
    scaled A a (5:Fin 10)=hzero d (nodes A (5:Fin 10)) := by
  rw [scaled_eval,R.sixth.rawH,hzero]
  field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an] <;> eight_ring K

theorem doubledScaled_ne {a d : K} (an : a≠0) (R : PhysicalPrefix A a d) :
    scaled A a (4:Fin 10)≠scaled A a (3:Fin 10) := by
  have e3 : h A (3:Fin 10)=a*d^2 := by
    simpa [chartH] using (R.first.features 3).2.2
  intro e
  rw [scaled_eval,scaled_eval,e3] at e
  exact R.fifth.2.2 ((div_left_inj₀ an).mp e)

noncomputable def wSlope (d : K) : K[X] :=
  C (-(4*d/5))*((X:K[X])^2-C (2*d^2))

theorem wSlope_eval (d x : K) :
    (wSlope d).eval x=-(4*d/5)*(x^2-2*d^2) := by simp [wSlope]

theorem wSlope_degree (d : K) : (wSlope d).natDegree≤2 := by
  unfold wSlope
  exact (natDegree_C_mul_le _ _).trans (le_of_eq (natDegree_X_pow_sub_C (2*d^2)))

/-- The difference W has zero *polynomial* part. This is not a
vanishing-at-one assertion for a grade-five defect. -/
theorem cleanW (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (mEq : LinearMap.range (shortProfileMap A)=treeSpace A 5)
    {a d : K} {i j : Fin 10} (D : GlobalNormal A a d i j) (R : PhysicalPrefix A a d) :
    ∀ r : Fin 10, g A r=0 → wTest A a d r=scaled A a r*(wSlope d).eval (nodes A r) := by
  let z := nodes A (5:Fin 10)
  let H := scaled A a
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have f2 : nodes A (2:Fin 10)=d ∧ g A (2:Fin 10)=0 := by
    have e := R.first.features (2:Fin 4)
    simpa [chartNode,chartDefect] using And.intro e.1 e.2.1
  have f3 : nodes A (3:Fin 10)=2*d ∧ g A (3:Fin 10)=0 ∧ h A (3:Fin 10)=a*d^2 := by
    simpa [chartNode,chartDefect,chartH] using R.first.features 3
  obtain ⟨PJ,QJ,βJ,PJd,_,PJm,PRJ⟩ := defectProfile ho mEq an (jTest_mem ho a)
  obtain ⟨PW,QW,βW,PWd,QWd,PWm,PRW⟩ := defectProfile ho mEq an (wTest_mem ho a d)
  have Jline (r : Fin 10) (hr : r.val≤6) (rc : nodes A r=2*d) (rg : g A r=0) :
      d^4/3+H r*(-(4*d^2/3))=PJ.eval (2*d)+H r*QJ.eval (2*d) := by
    have jf := (causalJV ha D R hr rg).1
    change jTest A a r=jValue d z (nodes A r) (H r) at jf
    rw [rc,j_value_doubled d z (H r) dn] at jf
    have pr := PRJ r
    rw [rc,rg,mul_zero,add_zero,←scaled_eval] at pr
    rw [←pr,jf]
    eight_ring K
  have Wline (r : Fin 10) (hr : r.val≤6) (rc : nodes A r=2*d) (rg : g A r=0) :
      0+H r*((wSlope d).eval (2*d))=PW.eval (2*d)+H r*QW.eval (2*d) := by
    have wf := wActual ha D R hr rg
    change wTest A a d r+(4*d/5)*((nodes A r)^2-2*d^2)*H r =
      (nodes A r-2*d)*(nodes A r-z)*(4*d*H r-(nodes A r)^2*(nodes A r-2*d))/5 at wf
    simp only [rc,sub_self,zero_mul,zero_div] at wf
    have pr := PRW r
    rw [rc,rg,mul_zero,add_zero,←scaled_eval] at pr
    rw [←pr,wSlope_eval]
    linear_combination (norm := eight_ring K) -wf
  have df : H (4:Fin 10)≠H (3:Fin 10) := doubledScaled_ne an R
  have jp := (common_clock_affine_parameters df
    (Jline 3 (by decide) f3.1 f3.2.1) (Jline 4 (by decide) R.fifth.1 R.fifth.2.1)).1
  have wp := (common_clock_affine_parameters df
    (Wline 3 (by decide) f3.1 f3.2.1) (Wline 4 (by decide) R.fifth.1 R.fifth.2.1)).1
  have jpne : PJ.eval (2*d)≠0 := by
    rw [jp]
    exact div_ne_zero (pow_ne_zero 4 dn) (by eight_num)
  have P0 := proportional_eval ha ho PJd PWd PJm PWm jpne wp
  have Wrep (r : Fin 10) (rg : g A r=0) : wTest A a d r=H r*QW.eval (nodes A r) := by
    simpa only [P0,eval_zero,rg,mul_zero,zero_add,←scaled_eval] using PRW r
  have equalAt (r : Fin 10) (hr : r.val≤6) (rg : g A r=0) (hn : H r≠0)
      (prod : (nodes A r-2*d)*(nodes A r-z)*(4*d*H r-(nodes A r)^2*(nodes A r-2*d))=0) :
      (QW-wSlope d).eval (nodes A r)=0 := by
    have wf := wActual ha D R hr rg
    change wTest A a d r+(4*d/5)*((nodes A r)^2-2*d^2)*H r =
      (nodes A r-2*d)*(nodes A r-z)*(4*d*H r-(nodes A r)^2*(nodes A r-2*d))/5 at wf
    rw [prod,zero_div,Wrep r rg] at wf
    rw [eval_sub,wSlope_eval]
    apply mul_left_cancel₀ hn
    linear_combination (norm := eight_ring K) wf
  have h2 : H (2:Fin 10)=hzero d d := scaledAtTwo D R
  have h3 : H (3:Fin 10)=d^2 := by
    change scaled A a (3:Fin 10)=_
    rw [scaled_eval,f3.2.2]
    field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an] <;> eight_ring K
  have h5 : H (5:Fin 10)=hzero d z := scaledAtFive an R
  have e2 : (QW-wSlope d).eval d=0 := by
    have e := equalAt 2 (by decide) f2.2 (by rw [h2]; exact height_ne d d dn dn (d_ne_double dn))
      (by simp only [f2.1,h2,height_identity d d dn,sub_self,mul_zero])
    simpa only [f2.1] using e
  have e3 : (QW-wSlope d).eval (2*d)=0 := by
    have e := equalAt 3 (by decide) f3.2.1 (by rw [h3]; exact pow_ne_zero 2 dn)
      (by simp only [f3.1,sub_self,zero_mul])
    simpa only [f3.1] using e
  have e5 : (QW-wSlope d).eval z=0 :=
    equalAt 5 (by decide) R.sixth.clean (by rw [h5]; exact height_ne d z dn R.sixth.notZero R.sixth.notDouble)
      (by change (z-2*d)*(z-z)*_ = 0; simp only [sub_self,mul_zero,zero_mul])
  have eq := sub_eq_zero.mp (poly_three_roots_zero
    ((natDegree_sub_le _ _).trans (max_le QWd (wSlope_degree d)))
    (d_ne_double dn) (Ne.symm R.sixth.notD) (Ne.symm R.sixth.notDouble) e2 e3 e5)
  intro r rg
  rw [Wrep r rg,eq]

theorem seventhAlternative (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (mEq : LinearMap.range (shortProfileMap A)=treeSpace A 5)
    {a d : K} {i j : Fin 10} (D : GlobalNormal A a d i j) (R : PhysicalPrefix A a d) :
    let x := nodes A (6:Fin 10)
    let z := nodes A (5:Fin 10)
    x=z ∨ scaled A a (6:Fin 10)=hzero d x := by
  let r : Fin 10 := 6
  let x := nodes A r
  let z := nodes A (5:Fin 10)
  let H := scaled A a r
  have wf := wActual ha D R (r:=r) (by decide) R.seventh.1
  change wTest A a d r+(4*d/5)*(x^2-2*d^2)*H=(x-2*d)*(x-z)*(4*d*H-x^2*(x-2*d))/5 at wf
  have zeroL : wTest A a d r+(4*d/5)*(x^2-2*d^2)*H=0 := by
    rw [cleanW ha ho mEq D R r R.seventh.1,wSlope_eval]
    change H*(-(4*d/5)*(x^2-2*d^2))+(4*d/5)*(x^2-2*d^2)*H=0
    eight_ring K
  rw [zeroL] at wf
  have prod := (div_eq_zero_iff.mp wf.symm).resolve_right (by eight_num : (5:K)≠0)
  by_cases same : x=z
  · exact Or.inl same
  · refine Or.inr ?_
    have e := (mul_eq_zero.mp prod).resolve_left
      (mul_ne_zero (sub_ne_zero.mpr R.seventh.2) (sub_ne_zero.mpr same))
    change H=x^2*(x-2*d)/(4*d)
    exact (eq_div_iff (mul_ne_zero (by eight_num : (4:K)≠0) D.base.dn)).mpr
      (by linear_combination (norm := eight_ring K) e)

/-- The terminal curve has at most two roots away from zero and the
doubled clock. Its residual quadratic is genuinely nonzero. -/
theorem curveClockTrap {d ρ z x : K} (dn : d≠0)
    (lD : (lobattoCubic : K[X]).eval (2*d)=0)
    (zn : z≠0) (zd : z≠d) (zD : z≠2*d) (xn : x≠0) (xD : x≠2*d)
    (fd : 14*d*(lobattoCubic : K[X]).eval d+hzero d d*(ρ*(d-2*d))=0)
    (fz : 14*z*(lobattoCubic : K[X]).eval z+hzero d z*(ρ*(z-2*d))=0)
    (fx : 14*x*(lobattoCubic : K[X]).eval x+hzero d x*(ρ*(x-2*d))=0) :
    x=d ∨ x=z := by
  obtain ⟨L,eL⟩ := dvd_iff_isRoot.mpr (show (lobattoCubic : K[X]).IsRoot (2*d) from lD)
  have base : (lobattoCubic : K[X]).eval 0≠0 := by
    rw [lobatto_eval_factor]
    simp [two_paid K,seven_paid K]
  have Ln : L.eval 0≠0 := by
    intro h
    apply base
    rw [eL,eval_mul,h,mul_zero]
  have Lne : L≠0 := by intro e; exact Ln (by rw [e,eval_zero])
  have cd : (lobattoCubic : K[X]).natDegree≤3 := by
    change (LobattoEight.lobattoCubic : K[X]).natDegree≤3
    exact (ERK8PaidField.lobattoCubic_degree_paid (K:=K)).le
  have Ld : L.natDegree≤2 := by
    have e := natDegree_mul (X_sub_C_ne_zero (2*d)) Lne
    rw [←eL,natDegree_X_sub_C] at e
    omega
  let M := C (14:K)*L+C (ρ/(4*d))*(X*(X-C (2*d)))
  have Md : M.natDegree≤2 := by
    apply natDegree_add_le_of_le (m:=2) (n:=2)
    · exact (natDegree_C_mul_le _ _).trans Ld
    · apply (natDegree_C_mul_le _ _).trans
      rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero _),natDegree_X,natDegree_X_sub_C]
  have Mval (u : K) : M.eval u=14*L.eval u+(ρ/(4*d))*u*(u-2*d) := by
    simp only [M,eval_add,eval_mul,eval_sub,eval_C,eval_X]
    eight_ring K
  have Mn : M.eval 0≠0 := by
    simpa only [Mval,mul_zero,zero_mul,add_zero] using
      (mul_ne_zero (by eight_num : (14:K)≠0) Ln)
  have root (u : K) (un : u≠0) (ud : u≠2*d)
      (f : 14*u*(lobattoCubic : K[X]).eval u+hzero d u*(ρ*(u-2*d))=0) :
      M.eval u=0 := by
    have F : u*(u-2*d)*M.eval u=0 := by
      rw [Mval]
      rw [eL,eval_mul,eval_sub,eval_X,eval_C,hzero] at f
      linear_combination (norm := eight_ring K) f
    exact (mul_eq_zero.mp F).resolve_left (mul_ne_zero un (sub_ne_zero.mpr ud))
  by_cases xd : x=d
  · exact Or.inl xd
  by_cases xz : x=z
  · exact Or.inr xz
  have eq := poly_three_roots_zero Md (Ne.symm zd) (Ne.symm xd) (Ne.symm xz)
    (root d dn (d_ne_double dn) fd) (root z zn zD fz) (root x xn xD fx)
  exact (Mn (by rw [eq,eval_zero])).elim

/-- Close on the same physical rows. This internal join is fed only by
the derived Fin 10 prefix; no external rows, ranks, or moment callbacks. -/
theorem finish (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (mid : ERKEvenHorizon A b 4)
    (rk : finrank K (treeSpace A 5)=9) (mEq : LinearMap.range (shortProfileMap A)=treeSpace A 5)
    {a d : K} {i j : Fin 10} (D : GlobalNormal A a d i j) (R : PhysicalPrefix A a d) : False := by
  let r : Fin 10 := 6
  let x := nodes A r
  let z := nodes A (5:Fin 10)
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have f0 : nodes A (0:Fin 10)=0 ∧ g A (0:Fin 10)=0 ∧ h A (0:Fin 10)=0 := by
    simpa [chartNode,chartDefect,chartH] using R.first.features 0
  have f2 : nodes A (2:Fin 10)=d ∧ g A (2:Fin 10)=0 := by
    have e := R.first.features (2:Fin 4)
    simpa [chartNode,chartDefect] using And.intro e.1 e.2.1
  have H2 := scaledAtTwo D R
  have H5 := scaledAtFive an R
  obtain ⟨ρ,lD,T⟩ := terminalProfile ho mid D R
  have t2 := T 2 (by decide) f2.2
  have t5 := T 5 (by decide) R.sixth.clean
  have t6 := T r (by decide) R.seventh.1
  rw [f2.1,H2] at t2
  rw [H5] at t5
  have same : x=z := by
    rcases seventhAlternative ha ho mEq D R with equal|curve
    · exact equal
    · by_contra xz
      have xn : x≠0 := by
        intro x0
        have e : scaled A a r=h A (0:Fin 10)/a := by
          change scaled A a (6:Fin 10)=h A (0:Fin 10)/a
          rw [curve,show nodes A (6:Fin 10)=0 from x0,f0.2.2]
          simp [hzero]
        rw [scaled_eval] at e
        exact noRepeatedFeature ha ho rk mEq R.sixth.beforeSeven (by decide : (0:Fin 10)<r)
          (f0.1.trans x0.symm) (f0.2.1.trans R.seventh.1.symm) ((div_left_inj₀ an).mp e).symm
      have tx := t6
      rw [curve] at tx
      have xd := (curveClockTrap dn lD R.sixth.notZero R.sixth.notD R.sixth.notDouble
        xn R.seventh.2 t2 t5 tx).resolve_right xz
      have hr : scaled A a r=scaled A a (2:Fin 10) := by
        change scaled A a (6:Fin 10)=scaled A a (2:Fin 10)
        rw [curve,H2,show nodes A (6:Fin 10)=d from xd]
      rw [scaled_eval,scaled_eval] at hr
      exact noRepeatedFeature ha ho rk mEq R.sixth.beforeSeven (by decide : (2:Fin 10)<r)
        (f2.1.trans xd.symm) (f2.2.trans R.seventh.1.symm) ((div_left_inj₀ an).mp hr).symm
  have dif : scaled A a r≠scaled A a (5:Fin 10) := by
    intro eq
    rw [scaled_eval,scaled_eval] at eq
    exact noRepeatedFeature ha ho rk mEq R.sixth.beforeSeven (by decide : (5:Fin 10)<r)
      same.symm (R.sixth.clean.trans R.seventh.1.symm) ((div_left_inj₀ an).mp eq).symm
  change 14*x*(lobattoCubic : K[X]).eval x+scaled A a r*(ρ*(x-2*d))=0 at t6
  rw [same] at t6
  have t5' := T 5 (by decide) R.sixth.clean
  change 14*z*(lobattoCubic : K[X]).eval z+scaled A a (5:Fin 10)*(ρ*(z-2*d))=0 at t5'
  have slope0 : ρ*(z-2*d)=0 := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr dif)
    linear_combination (norm := eight_ring K) t6-t5'
  have rho0 := (mul_eq_zero.mp slope0).resolve_right (sub_ne_zero.mpr R.sixth.notDouble)
  rw [rho0,zero_mul,mul_zero,add_zero] at t2
  have ld : (lobattoCubic : K[X]).eval d=0 :=
    (mul_eq_zero.mp t2).resolve_left (mul_ne_zero (by eight_num) dn)
  exact EightPaid.lobatto_no_doubled_root_paid ho ld lD

end RKResearch.Certified.Graded.OneOff.PaidProof.Eight
