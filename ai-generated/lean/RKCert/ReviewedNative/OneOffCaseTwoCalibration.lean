module

public import RKCert.ReviewedNative.OneOffSources

@[expose] public section

/-! # Physical calibration of the independent-square, on-first chart -/
namespace RKResearch.Certified.Graded.OneOff
open Module
open scoped Classical Matrix

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K}

abbrev twoHd (a d : K) := -a*d^2/4
abbrev twoGam (a d : K) := -a*(3*d-2*a)/(2*d)
abbrev twoLam (a d : K) := 4*d/(3*a)-2
abbrev twoMu (a d : K) := (d^2-2*a^2)/a
abbrev twoNu (a d v : K) := -(a-d)^2/(2*v)
abbrev twoKap (a d v : K) := a*(d-a)/(2*v)

noncomputable def zTwo (A : Matrix (Fin s) (Fin s) K) (a : K) : Fin s → K :=
  (g A)^2-(baseAmp a) • g A

omit [CharZero K] in
theorem zTwo_apply (A : Matrix (Fin s) (Fin s) K) (a : K) (i : Fin s) :
    zTwo A a i=g A i*(g A i-baseAmp a) := by
  simp [zTwo,pow_two,mul_sub,mul_comm]

/-- All normalizers have been justified on actual rows. No exceptional
condition on (a-2d) or (3d-2a) is included. -/
structure CaseTwo (A : Matrix (Fin s) (Fin s) K) (a d v : K) : Prop where
  an : a≠0
  dn : d≠0
  da : d≠a
  vn : v≠0
  changed : v≠baseAmp a
  q2 : mDef A 2=(2*a/3) • g A+twoLam a d • h A
  q3 : mDef A 3=((a^2/2) • g A+twoMu a d • h A)+twoNu a d v • zTwo A a
  hk : k A=twoKap a d v • zTwo A a
  offH : ∀ i, g A i≠0 → h A i=(twoGam a d/v)*zTwo A a i
  onH : ∀ i, g A i=0 → nodes A i≠d → h A i=0

theorem case_two_calibration (ha : ∀ i j, i ≤ j → A i j = 0) (sep : PolySeparated A 4)
    {a lam : K} {i j : Fin s} (O : Origin A a i) (F : FirstH A a lam j)
    (Q2 : mDef A 2=(2*a/3) • g A+lam • h A)
    (D : IndependentShape A a lam i j) (gj : g A j=0) :
    ∃ v : K, CaseTwo A a (nodes A j) v := by
  let d := nodes A j
  have on : d≠0 ∧ h A j=twoHd a d ∧ lam=twoLam a d := by
    rcases F.alternative with u|u
    · exact u.2
    · exact (u.1 gj).elim
  obtain ⟨dn,_,lam'⟩ := on
  subst lam
  have replace : correctedSquare A a j=zTwo A a := (corrected_square_values F).1 gj
  obtain ⟨eta,kap,mu,nu,cLaw,kLaw,qLaw,muOn,_⟩ := D.relations
  have mu' : mu=twoMu a d := muOn gj
  subst mu
  rw [replace] at cLaw kLaw qLaw
  have C (l : Fin s) : (nodes A l-d)*h A l=eta*zTwo A a l := by
    have e := congrFun cLaw l
    simp only [diag_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at e
    linear_combination e
  have Krow (l : Fin s) : k A l=kap*zTwo A a l := by
    simpa only [Pi.smul_apply,smul_eq_mul] using congrFun kLaw l
  have znot : zTwo A a≠0 := by
    intro e
    exact D.zout (by rw [replace,e]; exact (zeroSpace A 3).zero_mem)
  obtain ⟨l,zn,zpre⟩ := exists_first_nonzero znot
  let v := g A l
  have vprod : v*(v-baseAmp a)≠0 := by
    have e := zTwo_apply A a l
    rwa [←e]
  have vn := left_ne_zero_of_mul vprod
  have wn := right_ne_zero_of_mul vprod
  have vc : v≠baseAmp a := sub_ne_zero.mp wn
  have la : nodes A l=a := O.off_support l vn
  have da : d≠a := by
    intro eq
    have atL := C l
    rw [la,eq,sub_self,zero_mul] at atL
    have eta0 := (mul_eq_zero.mp atL.symm).resolve_right zn
    apply c4_support_one_impossible ha sep a
    intro l outside
    have z : g A l=0 := by by_contra n; exact outside (O.off_support l n)
    have w : zTwo A a l=0 := by simp [zTwo_apply,z]
    have ce := C l
    rw [eq,eta0,zero_mul] at ce
    have w' := (mul_eq_zero.mp ce).resolve_left (sub_ne_zero.mpr outside)
    exact ⟨z,by rw [Q2]; simp [z,w'],by rw [qLaw]; simp [z,w,w']⟩
  have hon (r : Fin s) (rg : g A r=0) (rd : nodes A r≠d) : h A r=0 := by
    have e := C r
    rw [zTwo_apply,rg,zero_mul,mul_zero] at e
    exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr rd)
  have hdN : twoHd a d≠0 := div_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr O.a_ne) (pow_ne_zero 2 dn)) (by norm_num)
  have fixed (r : Fin s) (rl : r < l) :
      ThreeFeatures a d (twoHd a d) (nodes A r) (g A r) (h A r) := by
    revert rl
    refine wellFounded_lt.induction (C:=fun r : Fin s=> r < l →
      ThreeFeatures a d (twoHd a d) (nodes A r) (g A r) (h A r)) r ?_
    intro r ih rl
    have pre (e : Fin s) (er : e < r) := ih e er (er.trans rl)
    obtain ⟨Act,_,_⟩ := three_sources_actions ha r O.a_ne hdN pre
    rw [Krow r,zpre r rl,mul_zero,mul_zero,add_zero] at Act
    have row := m1_relation A r
    by_cases ht : h A r=0
    · rw [Act,ht,mul_zero] at row
      have gd : g A r= -(nodes A r)^2/2 := by linear_combination -row
      by_cases zr : nodes A r=0
      · exact Or.inl ⟨zr, by rw [gd,zr]; simp, ht⟩
      · have ng : g A r≠0 := by
          rw [gd]
          exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 zr)) (by norm_num)
        have ca := O.off_support r ng
        exact Or.inr (Or.inl ⟨ca,by rw [gd,ca],ht⟩)
    · have c := C r
      rw [zpre r rl,mul_zero] at c
      have cd := sub_eq_zero.mp ((mul_eq_zero.mp c).resolve_right ht)
      have gg : g A r=0 := by
        by_contra ng
        exact da (cd.symm.trans (O.off_support r ng))
      rw [cd,gg,add_zero,Act] at row
      have hh : h A r=twoHd a d := by
        have ub : baseAmp a≠0 := div_ne_zero
          (neg_ne_zero.mpr (pow_ne_zero 2 O.a_ne)) (by norm_num)
        apply mul_left_cancel₀ (div_ne_zero O.a_ne ub)
        rw [row]
        field_simp [O.a_ne]
        ring
      exact Or.inr (Or.inr ⟨cd,gg,hh⟩)
  obtain ⟨M₁,M₂,M₃⟩ := three_sources_actions ha l O.a_ne hdN fixed
  let W := v-baseAmp a
  have row1 : M1 A l=W := by
    rw [m1_relation,la]
    change a^2/2+v=v-(-a^2/2)
    ring
  have a1 : a*d*W= -2*d*h A l-4*k A l := by
    rw [←row1,M₁]
    field_simp [O.a_ne,dn]
    ring
  have a2 : 2*a^2*W+4*d*h A l= -12*k A l := by
    have ml : 3*a*M2 A l= -6*a*h A l-12*k A l := by
      rw [M₂]
      field_simp [O.a_ne,dn]; ring
    have mr : 3*a*M2 A l=2*a^2*W+(4*d-6*a)*h A l := by
      rw [m2_relation Q2,la]
      change 3*a*(a^3/3+(2*a/3)*v+(4*d/(3*a)-2)*h A l)=
        2*a^2*(v-(-a^2/2))+(4*d-6*a)*h A l
      field_simp [O.a_ne]; ring
    linear_combination ml-mr
  have hscl : 2*d*h A l= -a*(3*d-2*a)*W := by linear_combination 3*a1-a2
  have kscl : 2*k A l=a*(d-a)*W := by linear_combination (1/2:K)*(a2-2*a1)
  have hnew : h A l=twoGam a d*W := by
    have e : (2*d)*twoGam a d= -a*(3*d-2*a) := by
      field_simp [dn]
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num) dn : 2*d≠0)
    rw [←mul_assoc,e]
    exact hscl
  have knw : k A l=kap*(v*W) := by simpa only [zTwo_apply] using Krow l
  have kap' : kap=twoKap a d v := by
    have r : kap*v=a*(d-a)/2 := by
      apply mul_right_cancel₀ wn
      linear_combination -knw+(1/2:K)*kscl
    apply (eq_div_iff (show (2:K)*v≠0 from mul_ne_zero (by norm_num) vn)).mpr
    linear_combination 2*r
  have a3 : (a^3/2)*W+d^2*h A l+4*d*k A l+a*nu*v*W=0 := by
    have ml : a*M3 A l= -2*a^2*h A l-4*d*k A l := by
      rw [M₃]
      field_simp [O.a_ne,dn]; ring
    have mr : a*M3 A l=(a^3/2)*W+(d^2-2*a^2)*h A l+a*nu*v*W := by
      rw [m3_relation qLaw,la,zTwo_apply]
      change a*(a^4/4+(a^2/2)*v+((d^2-2*a^2)/a)*h A l+
        nu*(v*(v-(-a^2/2))))=(a^3/2)*(v-(-a^2/2))+(d^2-2*a^2)*h A l+
          a*nu*v*(v-(-a^2/2))
      field_simp [O.a_ne]; ring
    linear_combination ml-mr
  have nu' : nu=twoNu a d v := by
    have P : a*W*(nu*v+(a-d)^2/2)=0 := by
      linear_combination a3-(d/2)*hscl-2*d*kscl
    have z := (mul_eq_zero.mp P).resolve_left (mul_ne_zero O.a_ne wn)
    apply (eq_div_iff (show (2:K)*v≠0 from mul_ne_zero (by norm_num) vn)).mpr
    linear_combination 2*z
  have etaV : eta*v=(a-d)*twoGam a d := by
    have e := C l
    rw [la,hnew,zTwo_apply] at e
    apply mul_right_cancel₀ wn
    linear_combination -e
  have opt (r : Fin s) (rg : g A r≠0) : h A r=(twoGam a d/v)*zTwo A a r := by
    have e := C r
    rw [O.off_support r rg] at e
    apply mul_right_cancel₀ vn
    have e0 : ((twoGam a d/v)*zTwo A a r)*v=twoGam a d*zTwo A a r := by
      rw [mul_right_comm,div_mul_cancel₀ _ vn]
    rw [e0]
    apply mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm da))
    linear_combination v*e+zTwo A a r*etaV
  refine ⟨v,⟨O.a_ne,dn,da,vn,vc,Q2,?_,?_,opt,hon⟩⟩
  · simpa only [nu'] using qLaw
  · simpa only [kap'] using kLaw

end RKResearch.Certified.Graded.OneOff
