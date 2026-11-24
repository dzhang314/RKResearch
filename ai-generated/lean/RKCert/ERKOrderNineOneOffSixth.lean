module

public import RKCert.ERKOrderNineOneOffCausalPrefix
public import RKCert.ERKOrderNineOneOffMaximal

@[expose] public section

/-! # Sixth stage: a third genuinely distinct clean clock -/
namespace RKCert.Paired.OneOff
open Module Polynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {A : Fin 12→Fin 12→K} {b : Vec K 12}

/-- Turn a signed affine relation at a single clock into the native
annihilator contradiction. Taking both prior indices equal also gives
the two-row special case. -/
theorem order9_no_interpolated_feature (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (rk : finrank K (treeSpace A 5)=10) (mEq : LinearMap.range (normalProfileMap A)=treeSpace A 5)
    {l m r : Fin 12} (pre : IndependentBefore (treeSpace A 4) r) (lr : l < r) (mr : m < r)
    (lc : nodes A l=nodes A r) (mc : nodes A m=nodes A r) (α : K)
    (gg : g A r=(1-α)*g A l+α*g A m) (hh : h A r=(1-α)*h A l+α*h A m) :
    False := by
  let w : Vec K 12 := (1-α) • Pi.single l 1+α • Pi.single m 1
  have act (v : Vec K 12) : row w v=(1-α)*v l+α*v m := by
    have rw_single (j : Fin 12) : row (Pi.single j (1:K)) v=v j := by
      simp [row_apply,Pi.single_apply]
    change rowL ((1-α) • Pi.single l (1:K)+α • Pi.single m 1) v=_
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
      rowL_apply,smul_eq_mul,rw_single]
  apply order9_forbid_same_clock_interpolation ha ho rk pre (w:=w)
  · intro i ir
    have il : i≠l := ne_of_gt (lr.trans_le ir)
    have im : i≠m := ne_of_gt (mr.trans_le ir)
    simp [w,Pi.single_apply,il,im]
  · intro i iw
    by_cases il : i=l
    · simpa only [il] using lc
    by_cases im : i=m
    · simpa only [im] using mc
    · exact (iw (by simp [w,Pi.single_apply,il,im])).elim
  · intro v hv
    rw [←mEq] at hv
    obtain ⟨f,rfl⟩ := hv
    rw [act,normal_profile_value,normal_profile_value,normal_profile_value,lc,mc,gg,hh]
    ring

theorem order9_no_repeated_feature (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (rk : finrank K (treeSpace A 5)=10) (mEq : LinearMap.range (normalProfileMap A)=treeSpace A 5)
    {l r : Fin 12} (pre : IndependentBefore (treeSpace A 4) r) (lr : l < r)
    (lc : nodes A l=nodes A r) (gc : g A l=g A r) (hc : h A l=h A r) :
    False :=
  order9_no_interpolated_feature ha ho rk mEq pre lr lr lc lc 0
    (by simp [gc]) (by simp [hc])

theorem cleanClockTest_mem (A : Fin 12→Fin 12→K) (a d : K) :
    cleanClockTest A a d∈treeSpace A 4 := by
  have cp (n : ℕ) (nd : n≤4) : (nodes A)^n∈treeSpace A 4 := by
    have e : evalNodes A ((X:K[X])^n)=(nodes A)^n := by ext l; simp
    rw [←e]
    exact evalNodes_mem_treeSpace A _ (by simp [nd])
  refine (treeSpace A 4).add_mem ?_ ((treeSpace A 4).smul_mem _
    (treeSpace_mono _ (by decide : 2≤4) (zeroSpace_le_treeSpace A 2 (qdef_mem A))))
  apply (treeSpace A 4).add_mem
  · exact (treeSpace A 4).sub_mem (cp 3 (by decide)) ((treeSpace A 4).smul_mem _ (cp 2 (by decide)))
  · simpa only [pow_one] using (treeSpace A 4).smul_mem (2*d^2) (cp 1 (by decide))

theorem order9_cleanClockTest_initial_zero (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (oneOff : (supportedNodes A (g A)).card=1)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j)
    (F : FirstFour A a d (by decide)) {r : Fin 12} (lr : r.val<5) :
    cleanClockTest A a d r=0 := by
  by_cases old : r.val<4
  · let l : Fin 4 := ⟨r.val,old⟩
    have e : Fin.castLE (by decide : 4≤12) l=r := Fin.ext rfl
    have fl := F.features l
    rw [e] at fl
    rw [cleanClockTest_apply,fl.1,fl.2.1]
    clear fl e
    generalize l=t
    have an := D.base.origin.a_ne
    fin_cases t <;> norm_num [chartNode,chartDefect,baseAmp] <;>
      (try field_simp [an]) <;> (first | exact an | ring)
  · have rr : r=(4:Fin 12) := Fin.ext (by omega)
    rw [rr]
    have f := order9_fifth_feature ha ho oneOff D F
    simp [cleanClockTest_apply,f.1,f.2.1]

theorem order9_sixth_feature (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (oneOff : (supportedNodes A (g A)).card=1)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j)
    (F : FirstFour A a d (by decide)) :
    let z := nodes A (5:Fin 12)
    g A (5:Fin 12)=0 ∧ z≠0 ∧ z≠d ∧ z≠2*d ∧ h A (5:Fin 12)=a*z^2*(z-2*d)/(4*d) ∧
    IndependentBefore (treeSpace A 4) (6:Fin 12) := by
  let r : Fin 12 := 5
  let z := nodes A r
  let H := h A r
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have ind := order9_first_five_independent ha ho oneOff D F
  obtain ⟨rk,mEq,_,_⟩ := order9_maximal_normal_profile ha ho oneOff D F
  have f0 : nodes A (0:Fin 12)=0 ∧ g A (0:Fin 12)=0 ∧ h A (0:Fin 12)=0 := by
    simpa [chartNode,chartDefect,chartH] using F.features 0
  have f1 : nodes A (1:Fin 12)=a ∧ g A (1:Fin 12)=baseAmp a ∧ h A (1:Fin 12)=0 := by
    simpa [chartNode,chartDefect,chartH] using F.features 1
  have f2 : nodes A (2:Fin 12)=d ∧ g A (2:Fin 12)=0 ∧ h A (2:Fin 12)=twoHd a d := by
    simpa [chartNode,chartDefect,chartH] using F.features 2
  have f3 : nodes A (3:Fin 12)=2*d ∧ g A (3:Fin 12)=0 ∧ h A (3:Fin 12)=a*d^2 := by
    simpa [chartNode,chartDefect,chartH] using F.features 3
  have f4 := order9_fifth_feature ha ho oneOff D F
  have early (l : Fin 12) (lt : l < r) : cleanClockTest A a d l=0 :=
    order9_cleanClockTest_initial_zero ha ho oneOff D F lt
  have action := cleanClockTest_action D r
  rw [causal_mat ha r _ early] at action
  have g0 : g A r=0 := by
    by_contra off
    have gh := congrFun (order9_defects_separate ha ho oneOff D) r
    change g A r*h A r=0 at gh
    exact order9_no_repeated_feature ha ho rk mEq ind (show (1:Fin 12)<r by decide)
      (f1.1.trans (D.base.origin.off_support r off).symm)
      (f1.2.1.trans (amplitude_value D.base.amplitude off).symm)
      (f1.2.2.trans ((mul_eq_zero.mp gh).resolve_left off).symm)
  rw [g0,mul_zero,add_zero] at action
  change 0=z^2*(z-2*d)^2/4+(d/a)*(2*d-z)*H at action
  have newT : z≠2*d := by
    intro za
    let α := (H-h A (3:Fin 12))/(h A (4:Fin 12)-h A (3:Fin 12))
    have Diff : h A (4:Fin 12)-h A (3:Fin 12)≠0 := by
      rw [f3.2.2]
      exact sub_ne_zero.mpr f4.2.2
    have hh : h A r=(1-α)*h A (3:Fin 12)+α*h A (4:Fin 12) := by
      change H=_
      dsimp only [α]
      field_simp [Diff]
      ring
    exact order9_no_interpolated_feature ha ho rk mEq ind
      (show (3:Fin 12)<r by decide) (show (4:Fin 12)<r by decide)
      (f3.1.trans za.symm) (f4.1.trans za.symm) α
      (by rw [g0,f3.2.1,f4.2.1]; ring) hh
  have Hform : H=a*z^2*(z-2*d)/(4*d) := by
    apply mul_left_cancel₀ (mul_ne_zero (div_ne_zero dn an)
      (sub_ne_zero.mpr (Ne.symm newT)))
    have eq : (d/a)*(2*d-z)*(a*z^2*(z-2*d)/(4*d))= -(z^2*(z-2*d)^2/4) := by
      field_simp [an,dn]
      ring
    calc (d/a)*(2*d-z)*H = -(z^2*(z-2*d)^2/4) := by linear_combination -action
         _ = (d/a)*(2*d-z)*(a*z^2*(z-2*d)/(4*d)) := eq.symm
  have nz : z≠0 := by
    intro zz
    have H0 : h A r=0 := by change H=0; rw [Hform,zz]; simp
    exact order9_no_repeated_feature ha ho rk mEq ind (show (0:Fin 12)<r by decide)
      (f0.1.trans zz.symm) (f0.2.1.trans g0.symm) (f0.2.2.trans H0.symm)
  have nd : z≠d := by
    intro zz
    have Hd : h A r=twoHd a d := by
      change H=_
      rw [Hform,zz]
      unfold twoHd
      field_simp [dn]
      ring
    exact order9_no_repeated_feature ha ho rk mEq ind (show (2:Fin 12)<r by decide)
      (f2.1.trans zz.symm) (f2.2.1.trans g0.symm) (f2.2.2.trans Hd.symm)
  have nn : cleanClockTest A a d r≠0 := by
    rw [cleanClockTest_apply,g0,mul_zero,add_zero]
    exact mul_ne_zero (mul_ne_zero nz (sub_ne_zero.mpr nd)) (sub_ne_zero.mpr newT)
  exact ⟨g0,nz,nd,newT,Hform,
    extend_independent_before (j:=r) (r:=(6:Fin 12)) rfl ind (cleanClockTest_mem A a d) early nn⟩

end RKCert.Paired.OneOff
