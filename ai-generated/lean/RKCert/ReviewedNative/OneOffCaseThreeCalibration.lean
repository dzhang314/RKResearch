module

public import RKCert.ReviewedNative.OneOffCaseTwoCalibration

@[expose] public section

/-! # Physical calibration of the independent-square, off-first chart -/
namespace RKResearch.Certified.Graded.OneOff
open scoped Classical Matrix

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K}

abbrev threeHd (a d : K) := d^2*(2*d-3*a)/4
abbrev threeGam (a : K) := -a/2
abbrev threeNu (a d v : K) := -a*(a-d)^2/(2*v*(2*d-3*a))
abbrev threeKap (a d v : K) := -a^2*(d-a)/(2*v*(2*d-3*a))

noncomputable def zThree (A : Matrix (Fin s) (Fin s) K) (a v : K) : Fin s → K :=
  zTwo A a+(2*v/a) • h A

omit [CharZero K] in
theorem zThree_apply (A : Matrix (Fin s) (Fin s) K) (a v : K) (i : Fin s) :
    zThree A a v i=g A i*(g A i-baseAmp a)+(2*v/a)*h A i := by
  simp [zThree,zTwo_apply]

/-- The first on coordinate of the corrected innovation proves all
normalizers, including (d(2d-3a)
e0), before a division is made. -/
structure CaseThree (A : Matrix (Fin s) (Fin s) K) (a d v : K) : Prop where
  an : a≠0
  dn : d≠0
  da : d≠a
  vn : v≠0
  changed : v≠baseAmp a
  dNorm : 2*d-3*a≠0
  q2 : mDef A 2=(2*a/3) • g A+(-2/3:K) • h A
  q3 : mDef A 3=((a^2/2) • g A+(-a) • h A)+threeNu a d v • zThree A a v
  hk : k A=threeKap a d v • zThree A a v
  off : ∀ i, g A i≠0 → zThree A a v i=0 ∧
    h A i=(threeGam a/v)*(g A i*(g A i-baseAmp a))
  onH : ∀ i, g A i=0 → nodes A i≠d → h A i=0

theorem case_three_calibration (ha : ∀ i j, i ≤ j → A i j = 0) (sep : PolySeparated A 4)
    {a lam : K} {i j : Fin s} (O : Origin A a i) (F : FirstH A a lam j)
    (Q2 : mDef A 2=(2*a/3) • g A+lam • h A)
    (D : IndependentShape A a lam i j) (gj : g A j≠0) :
    ∃ d v : K, CaseThree A a d v := by
  let v := g A j
  have off : v≠baseAmp a ∧ nodes A j=a ∧ h A j= -a*(v+a^2/2)/2 ∧ lam= -2/3 := by
    rcases F.alternative with e|e
    · exact (gj e.1).elim
    · exact e.2
  obtain ⟨vc,ja,_,lam'⟩ := off
  subst lam
  have vn : v≠0 := gj
  have replace : correctedSquare A a j=zThree A a v := (corrected_square_values F).2 gj
  obtain ⟨eta,kap,mu,nu,cLaw,kLaw,qLaw,_,muOff⟩ := D.relations
  have mu' := muOff gj
  subst mu
  rw [replace,ja] at cLaw
  rw [replace] at kLaw qLaw
  have C (r : Fin s) : (nodes A r-a)*h A r=eta*zThree A a v r := by
    have e := congrFun cLaw r
    simp only [diag_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at e
    linear_combination e
  have etaN : eta≠0 := by
    intro e0
    apply c4_support_one_impossible ha sep a
    intro r outside
    have g0 : g A r=0 := by by_contra e; exact outside (O.off_support r e)
    have c := C r
    rw [e0,zero_mul] at c
    have h0 := (mul_eq_zero.mp c).resolve_left (sub_ne_zero.mpr outside)
    have z0 : zThree A a v r=0 := by simp [zThree_apply,g0,h0]
    exact ⟨g0,by rw [Q2]; simp [g0,h0],by rw [qLaw]; simp [g0,h0,z0]⟩
  have normal : (2*v/a : K)≠0 := div_ne_zero (mul_ne_zero (by norm_num) vn) O.a_ne
  let d := a+eta*(2*v/a)
  have da : d≠a := by
    intro e
    exact mul_ne_zero etaN normal (by change a+eta*(2*v/a)=a at e; linear_combination e)
  have zOff (r : Fin s) (n : g A r≠0) : zThree A a v r=0 := by
    have e := C r
    rw [O.off_support r n,sub_self,zero_mul] at e
    exact (mul_eq_zero.mp e.symm).resolve_left etaN
  have hOn (r : Fin s) (g0 : g A r=0) (nd : nodes A r≠d) : h A r=0 := by
    have e := C r
    rw [zThree_apply,g0,zero_mul,zero_add] at e
    have c : (nodes A r-d)*h A r=0 := by dsimp only [d]; linear_combination e
    exact (mul_eq_zero.mp c).resolve_left (sub_ne_zero.mpr nd)
  have znon : zThree A a v≠0 := by
    intro e
    exact D.zout (by rw [replace,e]; exact (zeroSpace A 3).zero_mem)
  obtain ⟨l,zn,zpre⟩ := exists_first_nonzero znon
  have gl : g A l=0 := by by_contra gn; exact zn (zOff l gn)
  have zl : zThree A a v l=(2*v/a)*h A l := by simp [zThree_apply,gl]
  have hl : h A l≠0 := by intro e; exact zn (by rw [zl,e,mul_zero])
  have cl : nodes A l=d := by by_contra e; exact hl (hOn l gl e)
  have preOnH (r : Fin s) (rl : r < l) (g0 : g A r=0) : h A r=0 := by
    have e := zpre r rl
    rw [zThree_apply,g0,zero_mul,zero_add] at e
    exact (mul_eq_zero.mp e).resolve_left normal
  have preOnClock (r : Fin s) (rl : r < l) (g0 : g A r=0)
      (p : ∀ u, u < r → nodes A u=0 ∨ nodes A u=a) : nodes A r=0 := by
    have h0 := preOnH r rl g0
    apply c4_one_clock_next ha a r p g0
    · rw [Q2]
      simp [g0,h0]
    · rw [qLaw]
      simp [g0,h0,zpre r rl]
  have prev (r : Fin s) (rl : r < l) : nodes A r=0 ∨ nodes A r=a := by
    revert rl
    refine wellFounded_lt.induction (C:=fun r : Fin s=>r < l→nodes A r=0 ∨ nodes A r=a) r ?_
    intro r ih rl
    by_cases g0 : g A r=0
    · exact Or.inl (preOnClock r rl g0 (fun u hu=>ih u hu (hu.trans rl)))
    · exact Or.inr (O.off_support r g0)
  have hpre (r : Fin s) (rl : r < l) :
      h A r=(-a/2)*g A r-(a^2/4)*nodes A r := by
    have pp (u : Fin s) (ur : u < r) := prev u (ur.trans rl)
    by_cases g0 : g A r=0
    · simp [g0,preOnH r rl g0, preOnClock r rl g0 pp]
    · have cr := O.off_support r g0
      have e := m2_relation Q2 r
      have act : M2 A r=a*M1 A r := by
        simpa only [pow_one] using clock_power_action ha 1 pp
      rw [act,m1_relation,cr] at e
      rw [cr]
      linear_combination (3/2:K)*e
  have m1 : M1 A l=d^2/2 := by rw [m1_relation,cl,gl,add_zero]
  have m2 := m2_relation Q2 l
  have act2 : M2 A l=a*M1 A l := by
    simpa only [pow_one] using clock_power_action ha 1 prev
  rw [act2,m1,cl,gl] at m2
  simp only [mul_zero,add_zero] at m2
  have Hd : h A l=threeHd a d := by
    change h A l=d^2*(2*d-3*a)/4
    linear_combination (3/2:K)*m2
  have dn : d≠0 := by intro e; exact hl (by simp [Hd,e])
  have dm : 2*d-3*a≠0 := by intro e; exact hl (by simp only [Hd,threeHd,e,mul_zero,zero_div])
  have actualK : k A l= -a*d^2*(d-a)/4 := by
    have e := causal_action_eq ha l (h A) ((-a/2) • g A-(a^2/4) • nodes A)
      (fun r rl => by simpa only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] using hpre r rl)
    simp only [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,mat_g,m1,Hd] at e
    linear_combination e
  have aZ : a*zThree A a v l=v*d^2*(2*d-3*a)/2 := by
    rw [zl,Hd]
    field_simp [O.a_ne]; ring
  have den : (2:K)*v*(2*d-3*a)≠0 := mul_ne_zero (mul_ne_zero (by norm_num) vn) dm
  have kap' : kap=threeKap a d v := by
    have e : k A l=kap*zThree A a v l := by
      simpa only [Pi.smul_apply,smul_eq_mul] using congrFun kLaw l
    have e' := congrArg (a * ·) e
    rw [actualK,mul_left_comm a kap,aZ] at e'
    apply (eq_div_iff den).mpr
    apply mul_right_cancel₀ (pow_ne_zero 2 dn)
    linear_combination -4*e'
  have nu' : nu=threeNu a d v := by
    have q := m3_relation qLaw l
    have act3 : M3 A l=a^2*M1 A l := clock_power_action ha 2 prev
    rw [act3,m1,cl,gl,Hd,mul_zero,add_zero] at q
    have e : nu*zThree A a v l= -(d^2*(a-d)^2)/4 := by linear_combination -q
    have e' := congrArg (a * ·) e
    rw [mul_left_comm a nu,aZ] at e'
    apply (eq_div_iff den).mpr
    apply mul_right_cancel₀ (pow_ne_zero 2 dn)
    linear_combination 4*e'
  have ofH (r : Fin s) (ng : g A r≠0) :
      h A r=(threeGam a/v)*(g A r*(g A r-baseAmp a)) := by
    have e := zOff r ng
    rw [zThree_apply] at e
    have norm : (2*v/a)*(threeGam a/v)= -1 := by
      field_simp [O.a_ne,vn]
    apply mul_left_cancel₀ normal
    rw [←mul_assoc,norm]
    linear_combination e
  refine ⟨d,v,⟨O.a_ne,dn,da,vn,vc,dm,Q2,?_,?_,fun r nr=>⟨zOff r nr,ofH r nr⟩,hOn⟩⟩
  · simpa only [nu'] using qLaw
  · simpa only [kap'] using kLaw

end RKResearch.Certified.Graded.OneOff
