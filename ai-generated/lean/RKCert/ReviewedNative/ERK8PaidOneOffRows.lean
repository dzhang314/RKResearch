module
public import RKCert.ReviewedNative.ERK8PaidArithmetic

public import RKCert.ReviewedNative.ERK8PaidOneOffProfiles

@[expose] public section

/-! Source-only chronological one-off chart in the **original Fin 10**.
All no-interpolation payments here use p8, rank nine, reverse n=1. -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof.Eight

open RKResearch Module Reverse Polynomial
open scoped Classical Matrix

section GenericCausalIndependence
variable {K : Type*} [Field K] [EightUnits K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}

omit [EightUnits K] in
/-- Fill one chronological support position using one paid vector that
vanishes on the previous prefix. No matrix-rank recomputation. -/
theorem extend_independent_before {U : Submodule K (Fin s → K)} {j r : Fin s} {v : Fin s → K}
    (next : r.val=j.val+1) (ind : IndependentBefore U j)
    (vm : v∈U) (early : ∀ l, l < j → v l=0) (vn : v j≠0) :
    IndependentBefore U r := by
  intro w wm supp
  have e := (mem_annih.mp wm) _ vm
  change row w v=0 at e
  rw [row_apply,dotProduct,Finset.sum_eq_single j] at e
  · have wj := (mul_eq_zero.mp e).resolve_right vn
    apply ind w wm
    intro l jl
    by_cases hl : l=j
    · rw [hl,wj]
    · exact supp l (show r.val≤l.val by
        have ll : j.val≤l.val := jl
        have ne : l.val≠j.val := fun eq=>hl (Fin.ext eq)
        omega)
  · intro l _ ne
    by_cases hl : l < j
    · rw [early l hl,mul_zero]
    · rw [supp l (show r.val≤l.val by
        have ll : j.val≤l.val := le_of_not_gt hl
        have hv : l.val≠j.val := fun eq=>ne (Fin.ext eq)
        omega),zero_mul]
  · simp

theorem first_four_independent {a d : K} {r : Fin s} (an : a≠0) (dn : d≠0)
    (C : FirstChartBefore A a d r) :
    IndependentBefore (treeSpace A 4) r := by
  intro w wm supp
  apply prefix_row_zero_by_selectors an dn C supp
  intro l
  exact (mem_annih.mp wm) _ (treeSpace_mono A (by decide : 2≤4)
    (chart_selector_mem A a d l))

end GenericCausalIndependence

variable {K : Type*} [Field K] [EightUnits K] {A : Matrix (Fin 10) (Fin 10) K}
variable {b : Fin 10 → K}

theorem forbidSameClockInterpolation
    {A : Matrix (Fin 10) (Fin 10) K} {b w : Fin 10 → K} {j : Fin 10}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (rank : finrank K (treeSpace A 5)=9)
    (pre : IndependentBefore (treeSpace A 4) j)
    (prev : ∀ i, j ≤ i → w i=0)
    (clock : ∀ i, w i≠0 → nodes A i=nodes A j)
    (fit : ∀ v∈treeSpace A 5, v j=row w v) : False := by
  let q := coordinate (K:=K) j-w
  have qj : q j=1 := by simp [q,coordinate,prev j le_rfl]
  have qn : q≠0 := by intro e; rw [e] at qj; exact zero_ne_one qj
  have qr : q∈annih (treeSpace A 5) := by
    apply mem_annih.mpr
    intro v hv
    have e : row (coordinate j) v=v j := by
      rw [row_apply,dotProduct_comm,←row_apply,row_coordinate]
    change (coordinate (K:=K) j-w) ⬝ᵥ v=0
    rw [sub_dotProduct,←row_apply,←row_apply,e,fit _ hv,sub_self]
  apply noCausalClockContrast ha ho rank pre qr qn
  · intro i hi
    simp [q,coordinate,ne_of_gt hi,prev i hi.le]
  · intro i hi
    by_cases e : i=j
    · simp [e]
    · apply clock i
      intro z
      apply hi
      simp [q,coordinate,e,z]

theorem noInterpolatedFeature (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (rk : finrank K (treeSpace A 5)=9) (mEq : LinearMap.range (shortProfileMap A)=treeSpace A 5)
    {l m r : Fin 10} (pre : IndependentBefore (treeSpace A 4) r) (lr : l < r) (mr : m < r)
    (lc : nodes A l=nodes A r) (mc : nodes A m=nodes A r) (α : K)
    (gg : g A r=(1-α)*g A l+α*g A m) (hh : h A r=(1-α)*h A l+α*h A m) :
    False := by
  let w : Fin 10 → K := (1-α) • Pi.single l 1+α • Pi.single m 1
  have act (v : Fin 10 → K) : row w v=(1-α)*v l+α*v m := by
    have rw_single (j : Fin 10) : row (Pi.single j (1:K)) v=v j := by
      rw [row_apply,dotProduct_comm,dotProduct_single_one]
    simp only [w,row_apply,add_dotProduct,smul_dotProduct,smul_eq_mul]
    rw [←row_apply,←row_apply,rw_single,rw_single]
  apply forbidSameClockInterpolation ha ho rk pre (w:=w)
  · intro i ir
    have il : i≠l := ne_of_gt (lr.trans_le ir)
    have im : i≠m := ne_of_gt (mr.trans_le ir)
    simp [w,il,im]
  · intro i iw
    by_cases il : i=l
    · simpa only [il] using lc
    by_cases im : i=m
    · simpa only [im] using mc
    · exact (iw (by simp [w,il,im])).elim
  · intro v hv
    rw [←mEq] at hv
    obtain ⟨f,rfl⟩ := hv
    rw [act,shortProfile_value,shortProfile_value,shortProfile_value,lc,mc,gg,hh]
    eight_ring K

theorem noRepeatedFeature (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (rk : finrank K (treeSpace A 5)=9) (mEq : LinearMap.range (shortProfileMap A)=treeSpace A 5)
    {l r : Fin 10} (pre : IndependentBefore (treeSpace A 4) r) (lr : l < r)
    (lc : nodes A l=nodes A r) (gc : g A l=g A r) (hc : h A l=h A r) :
    False :=
  noInterpolatedFeature ha ho rk mEq pre lr lr lc lc 0
    (by simp [gc]) (by simp [hc])

theorem cleanClockTest_mem_eight (A : Matrix (Fin 10) (Fin 10) K) (a d : K) :
    cleanClockTest A a d∈treeSpace A 4 := by
  have cp (n : ℕ) (nd : n≤4) : (nodes A)^n∈treeSpace A 4 := by
    have e : evalNodes A ((X:K[X])^n)=(nodes A)^n := by ext l; simp
    rw [←e]
    exact evalNodes_mem_treeSpace A _ (by simp [nd])
  refine (treeSpace A 4).add_mem ?_ ((treeSpace A 4).smul_mem _
    (treeSpace_mono _ (by decide : 2≤4) (zeroSpace_le_treeSpace A 2 (mDef_mem A 1))))
  apply (treeSpace A 4).add_mem
  · exact (treeSpace A 4).sub_mem (cp 3 (by decide)) ((treeSpace A 4).smul_mem _ (cp 2 (by decide)))
  · simpa only [pow_one] using (treeSpace A 4).smul_mem (2*d^2) (cp 1 (by decide))

theorem firstFiveIndependent
    {a d : K} {i j : Fin 10} (D : GlobalNormal A a d i j)
    (F : FirstFour A a d (by decide))
    (f4 : nodes A (4:Fin 10)=2*d ∧ g A (4:Fin 10)=0 ∧ h A (4:Fin 10)≠a*d^2) :
    IndependentBefore (treeSpace A 4) (5:Fin 10) := by
  let r : Fin 10 := 4
  let V : Fin 10 → K := deltaH A d-(d*(a*d^2)) • chartSelector A a d 3
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have C : FirstChartBefore A a d r := firstChartBefore_four (by decide) rfl F
  have ind := first_four_independent an dn C
  have vm : V∈treeSpace A 4 := (treeSpace A 4).sub_mem
    (zeroSpace_le_treeSpace A 4 (deltaH_in_grade_four A d))
    ((treeSpace A 4).smul_mem _ (treeSpace_mono A (by decide : 2≤4) (chart_selector_mem A a d 3)))
  have van (u : Fin 10) (ur : u < r) : V u=0 := by
    obtain ⟨l,ll,cu,gu⟩ := C u ur
    have fu := F.features l
    rw [(Fin.ext ll : Fin.castLE (by decide : 4≤10) l=u)] at fu
    have sel := chart_selector_nodes an dn cu gu 3
    simp only [V,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,deltaH_apply,
      cu,fu.2.2,sel]
    clear sel fu gu cu ll ur
    fin_cases l <;> norm_num [chartNode,chartH]
    eight_ring K
  have sel : chartSelector A a d 3 r=1 := by
    have cn : nodes A r=chartNode a d 3 := by simpa [chartNode] using f4.1
    have cg : g A r=chartDefect a 3 := by simpa [chartDefect] using f4.2.1
    simpa using chart_selector_nodes an dn cn cg 3
  have cr : nodes A r=2*d := f4.1
  have vn : V r≠0 := by
    have ve : V r=d*(h A r-a*d^2) := by
      simp only [V,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,deltaH_apply,cr,sel,mul_one]
      eight_ring K
    rw [ve]
    exact mul_ne_zero dn (sub_ne_zero.mpr f4.2.2)
  exact extend_independent_before (j:=r) (r:=(5:Fin 10)) rfl ind vm van vn

theorem initialClockTestZero
    {a d : K} {i j : Fin 10} (D : GlobalNormal A a d i j)
    (F : FirstFour A a d (by decide))
    (f4 : nodes A (4:Fin 10)=2*d ∧ g A (4:Fin 10)=0 ∧ h A (4:Fin 10)≠a*d^2) {r : Fin 10} (lr : r.val<5) :
    cleanClockTest A a d r=0 := by
  by_cases old : r.val<4
  · let l : Fin 4 := ⟨r.val,old⟩
    have e : Fin.castLE (by decide : 4≤10) l=r := Fin.ext rfl
    have fl := F.features l
    rw [e] at fl
    rw [cleanClockTest_apply,fl.1,fl.2.1]
    clear fl e
    generalize l=t
    have an := D.base.origin.a_ne
    fin_cases t <;> norm_num [chartNode,chartDefect,baseAmp]
    field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an]
    eight_ring K
  · have rr : r=(4:Fin 10) := Fin.ext (by omega)
    rw [rr]
    simp [cleanClockTest_apply,f4.1,f4.2.1]

/-- Two doubled clean rows with different h forbid the next independent
receiver from being off or another row at the doubled clock. -/
theorem nextCleanOffDouble (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (rk : finrank K (treeSpace A 5)=9) (mEq : LinearMap.range (shortProfileMap A)=treeSpace A 5)
    (gh : g A*h A=0) {a d : K} {i j r : Fin 10} (D : GlobalNormal A a d i j)
    (F : FirstFour A a d (by decide))
    (f4 : nodes A (4:Fin 10)=2*d ∧ g A (4:Fin 10)=0 ∧ h A (4:Fin 10)≠a*d^2)
    (r4 : (4:Fin 10)<r) (ind : IndependentBefore (treeSpace A 4) r) :
    g A r=0 ∧ nodes A r≠2*d := by
  have f1 : nodes A (1:Fin 10)=a ∧ g A (1:Fin 10)=baseAmp a ∧ h A (1:Fin 10)=0 := by
    simpa [chartNode,chartDefect,chartH] using F.features 1
  have f3 : nodes A (3:Fin 10)=2*d ∧ g A (3:Fin 10)=0 ∧ h A (3:Fin 10)=a*d^2 := by
    simpa [chartNode,chartDefect,chartH] using F.features 3
  have g0 : g A r=0 := by
    by_contra off
    have e := congrFun gh r
    change g A r*h A r=0 at e
    exact noRepeatedFeature ha ho rk mEq ind ((by decide : (1:Fin 10)<4).trans r4)
      (f1.1.trans (D.base.origin.off_support r off).symm)
      (f1.2.1.trans (amplitude_value D.base.amplitude off).symm)
      (f1.2.2.trans ((mul_eq_zero.mp e).resolve_left off).symm)
  refine ⟨g0,?_⟩
  intro cr
  let α := (h A r-h A (3:Fin 10))/(h A (4:Fin 10)-h A (3:Fin 10))
  have diff : h A (4:Fin 10)-h A (3:Fin 10)≠0 := by
    rw [f3.2.2]
    exact sub_ne_zero.mpr f4.2.2
  have hh : h A r=(1-α)*h A (3:Fin 10)+α*h A (4:Fin 10) := by
    dsimp only [α]
    field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,diff] <;> eight_ring K
  exact noInterpolatedFeature ha ho rk mEq ind ((by decide : (3:Fin 10)<4).trans r4)
    r4 (f3.1.trans cr.symm) (f4.1.trans cr.symm) α
    (by rw [g0,f3.2.1,f4.2.1]; eight_ring K) hh

structure Sixth (A : Matrix (Fin 10) (Fin 10) K) (a d : K) : Prop where
  clean : g A (5:Fin 10)=0
  notZero : nodes A (5:Fin 10)≠0
  notD : nodes A (5:Fin 10)≠d
  notDouble : nodes A (5:Fin 10)≠2*d
  rawH : h A (5:Fin 10)=a*(nodes A (5:Fin 10))^2*(nodes A (5:Fin 10)-2*d)/(4*d)
  beforeSeven : IndependentBefore (treeSpace A 4) (6:Fin 10)

theorem sixthRow (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (rk : finrank K (treeSpace A 5)=9) (mEq : LinearMap.range (shortProfileMap A)=treeSpace A 5)
    (gh : g A*h A=0) {a d : K} {i j : Fin 10} (D : GlobalNormal A a d i j)
    (F : FirstFour A a d (by decide))
    (f4 : nodes A (4:Fin 10)=2*d ∧ g A (4:Fin 10)=0 ∧ h A (4:Fin 10)≠a*d^2) :
    Sixth A a d := by
  let r : Fin 10 := 5
  let z := nodes A r
  let H := h A r
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have ind := firstFiveIndependent D F f4
  have f0 : nodes A (0:Fin 10)=0 ∧ g A (0:Fin 10)=0 ∧ h A (0:Fin 10)=0 := by
    simpa [chartNode,chartDefect,chartH] using F.features 0
  have f2 : nodes A (2:Fin 10)=d ∧ g A (2:Fin 10)=0 ∧ h A (2:Fin 10)=twoHd a d := by
    simpa [chartNode,chartDefect,chartH] using F.features 2
  have early (l : Fin 10) (lt : l < r) : cleanClockTest A a d l=0 :=
    initialClockTestZero D F f4 lt
  obtain ⟨g0,notT⟩ := nextCleanOffDouble ha ho rk mEq gh D F f4 (show (4:Fin 10)<r by decide) ind
  have action := cleanClockTest_action D r
  rw [causal_mat ha r _ early,g0,mul_zero,add_zero] at action
  change 0=z^2*(z-2*d)^2/4+(d/a)*(2*d-z)*H at action
  have Hform : H=a*z^2*(z-2*d)/(4*d) := by
    apply mul_left_cancel₀ (mul_ne_zero (div_ne_zero dn an)
      (sub_ne_zero.mpr (Ne.symm notT)))
    have eq : (d/a)*(2*d-z)*(a*z^2*(z-2*d)/(4*d))= -(z^2*(z-2*d)^2/4) := by
      field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an,dn] <;> eight_ring K
    calc (d/a)*(2*d-z)*H = -(z^2*(z-2*d)^2/4) := by linear_combination (norm := eight_ring K) -action
         _ = (d/a)*(2*d-z)*(a*z^2*(z-2*d)/(4*d)) := eq.symm
  have nz : z≠0 := by
    intro zz
    have H0 : h A r=0 := by change H=0; rw [Hform,zz]; simp
    exact noRepeatedFeature ha ho rk mEq ind (show (0:Fin 10)<r by decide)
      (f0.1.trans zz.symm) (f0.2.1.trans g0.symm) (f0.2.2.trans H0.symm)
  have nd : z≠d := by
    intro zz
    have Hd : h A r=twoHd a d := by
      change H=_
      rw [Hform,zz]
      unfold twoHd
      field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,dn] <;> eight_ring K
    exact noRepeatedFeature ha ho rk mEq ind (show (2:Fin 10)<r by decide)
      (f2.1.trans zz.symm) (f2.2.1.trans g0.symm) (f2.2.2.trans Hd.symm)
  have nn : cleanClockTest A a d r≠0 := by
    rw [cleanClockTest_apply,g0,mul_zero,add_zero]
    exact mul_ne_zero (mul_ne_zero nz (sub_ne_zero.mpr nd)) (sub_ne_zero.mpr notT)
  exact ⟨g0,nz,nd,notT,Hform,
    extend_independent_before (j:=r) (r:=(6:Fin 10)) rfl ind (cleanClockTest_mem_eight A a d) early nn⟩

structure PhysicalPrefix (A : Matrix (Fin 10) (Fin 10) K) (a d : K) : Prop where
  first : FirstFour A a d (by decide)
  fifth : nodes A (4:Fin 10)=2*d ∧ g A (4:Fin 10)=0 ∧ h A (4:Fin 10)≠a*d^2
  sixth : Sixth A a d
  seventh : g A (6:Fin 10)=0 ∧ nodes A (6:Fin 10)≠2*d

/-- The actual ordered rows 0 through 6, with no rank, feature, or
chronology hypotheses supplied by the caller. -/
theorem physicalPrefix_of_horizon (ha : ∀ i j, i≤j → A i j=0)
    (ho : RKResearch.HasOrder 8 A b) (mid : ERKEvenHorizon A b 4)
    (off : (offKnots A).card=1) :
    ∃ (a d : K) (i j : Fin 10), GlobalNormal A a d i j ∧ PhysicalPrefix A a d ∧
      finrank K (treeSpace A 5)=9 ∧ LinearMap.range (shortProfileMap A)=treeSpace A 5 := by
  obtain ⟨sep,rk3,rk4⟩ := frontRanks ha ho mid
  obtain ⟨a,d,i,j,D⟩ := earnedNormal ha ho mid off
  have gh := defectsSeparate ha ho mid D
  obtain ⟨rk,mEq⟩ := shortProfileFull ha ho mid D
  have f := firstFour ha ho (by decide) sep rk3 rk4 D
  have f4 := fifthFeature ha ho sep rk3 rk4 gh D f
  have f5 := sixthRow ha ho rk mEq gh D f f4
  have f6 := nextCleanOffDouble ha ho rk mEq gh D f f4 (by decide) f5.beforeSeven
  exact ⟨a,d,i,j,D,⟨f,f4,f5,f6⟩,rk,mEq⟩

end RKResearch.Certified.Graded.OneOff.PaidProof.Eight
