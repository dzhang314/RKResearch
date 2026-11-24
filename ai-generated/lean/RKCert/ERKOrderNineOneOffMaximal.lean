module

public import RKCert.ERKOrderNineOneOffFifth
public import RKCert.ERKOrderNineOneOffProfileRank

@[expose] public section

/-! # Maximal grade five in the original twelve coordinates -/
namespace RKCert.Paired.OneOff
open Module Polynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {A : Fin 12→Fin 12→K} {b : Vec K 12}

noncomputable def clockAg (A : Fin 12→Fin 12→K) : Vec K 12 :=
  mat A (diag (nodes A) (h A))

theorem clockAg_mem (ho : HasTreeOrderAtLeast A b 9) :
    clockAg A∈zeroSpace A 5 :=
  mat_zeroSpace ho 4 (by decide) (diag_zeroSpace A 3 (h_in_grade_three A))

/-- One short causal identity gives both A(CAg) evaluations at the two
doubled-clock rows. The off source is corrected before applying A. -/
theorem clockAg_doubled (ha : StrictLower A) {a d : K} {i j r : Fin 12}
    (D : GlobalNormal A a d i j)
    (F : FirstFour A a d (by decide)) (r4 : r.val≤4)
    (cr : nodes A r=2*d) (gr : g A r=0) :
    clockAg A r=a*d^4/3+h A r*(-(4*d^2/3)) := by
  let U : Vec K 12 :=
    d • h A+(a*d/2) •
      ((nodes A)^2-d • nodes A-(a*(a-d)/baseAmp a) • g A)
  have an := D.base.origin.a_ne
  have act := causal_action_eq ha r (diag (nodes A) (h A)) U (fun l lr=>by
    have ll : l.val < r.val := lr
    let k : Fin 4 := ⟨l.val,ll.trans_le r4⟩
    have eq : Fin.castLE (by decide : 4≤12) k=l := Fin.ext rfl
    have f := F.features k
    rw [eq] at f
    simp only [U,diag_apply,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.pow_apply,smul_eq_mul,
      f.1,f.2.1,f.2.2]
    clear f eq
    generalize k = t
    fin_cases t <;>
      norm_num [chartNode,chartDefect,chartH,twoHd,baseAmp] <;>
      (try field_simp [an]) <;> (first | (simp [an,D.base.dn]; done) | ring))
  simp only [U,map_add,map_sub,map_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at act
  change clockAg A r=d*k A r+(a*d/2)*(M2 A r-d*M1 A r-(a*(a-d)/baseAmp a)*h A r) at act
  have kk : k A r=(d-nodes A r)*h A r := by
    rw [global_k_neg_delta D,Pi.neg_apply,deltaH_apply]
    ring
  rw [act,kk,m1_relation,m2_relation D.base.q2,cr,gr]
  dsimp only [twoLam,baseAmp]
  field_simp [an]
  ring

/-- Actual rank ten, native polynomial plus defect coordinates, a nonzero
anchored Radau value at the doubled clock, and distinction from the terminal. -/
theorem order9_maximal_normal_profile (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b 9) (oneOff : (supportedNodes A (g A)).card=1)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j)
    (F : FirstFour A a d (by decide)) :
    finrank K (treeSpace A 5)=10 ∧ LinearMap.range (normalProfileMap A)=treeSpace A 5 ∧
      (anchorRadau : K[X]).eval (2*d)≠0 ∧ 2*d≠1 := by
  let j3 : Fin 12 := 3
  let j4 : Fin 12 := 4
  let last : Fin 12 := Fin.last 11
  let P (w : NormalCoeffs K) := ofFn 6 w.1
  let Q (w : NormalCoeffs K) := ofFn 3 w.2.2
  have f3 : nodes A j3=2*d ∧ g A j3=0 ∧ h A j3=a*d^2 := by
    simpa [j3,chartNode,chartDefect,chartH] using F.features 3
  have f4 := order9_fifth_feature ha ho oneOff D F
  have dif : h A j4≠h A j3 := by simpa only [f3.2.2] using f4.2.2
  have interp (w : NormalCoeffs K) {c q : K}
      (e3 : c+h A j3*q=normalProfileMap A w j3)
      (e4 : c+h A j4*q=normalProfileMap A w j4) :
      (P w).eval (2*d)=c ∧ (Q w).eval (2*d)=q := by
    rw [normal_profile_value,f3.1,f3.2.1,mul_zero,zero_add] at e3
    rw [normal_profile_value,f4.1,f4.2.1,mul_zero,zero_add] at e4
    exact common_clock_affine_parameters dif e3 e4
  have lower := normal_profile_rank_nine ha ho oneOff D
  have upper := (order9_twelve_stage_chart ha ho).2.2.2.2.2.2.1
  have rangeSub := normal_profile_range_le ho
  have radau_ne (rangeEq : LinearMap.range (normalProfileMap A)=treeSpace A 5) :
      (anchorRadau : K[X]).eval (2*d)≠0 := by
    have hm : clockAg A∈LinearMap.range (normalProfileMap A) := by
      rw [rangeEq]
      exact zeroSpace_le_treeSpace A 5 (clockAg_mem ho)
    obtain ⟨w,hw⟩ := hm
    have dj : normalProfileMap A w∈zeroSpace A 5 := hw ▸ clockAg_mem ho
    have rad := normal_profile_defect_poly ha ho w dj
    have e3 : a*d^4/3+h A j3*(-(4*d^2/3))=normalProfileMap A w j3 :=
      (clockAg_doubled ha D F (show j3.val≤4 by decide) f3.1 f3.2.1).symm.trans
        (congrFun hw j3).symm
    have e4 : a*d^4/3+h A j4*(-(4*d^2/3))=normalProfileMap A w j4 :=
      (clockAg_doubled ha D F (show j4.val≤4 by decide) f4.1 f4.2.1).symm.trans
        (congrFun hw j4).symm
    have E := (interp w e3 e4).1
    change (ofFn 6 w.1).eval (2*d)=_ at E
    intro zero
    rw [rad,eval_mul,zero,mul_zero] at E
    exact (div_ne_zero (mul_ne_zero D.base.origin.a_ne (pow_ne_zero 4 D.base.dn))
      (by norm_num : (3:K)≠0)) E.symm
  have inject_by_radau (nz : (anchorRadau : K[X]).eval (2*d)≠0) :
      Function.Injective (normalProfileMap A) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro w ker
    have r := wide_kernel_poly ha ho (w,0) ((wide_at_normal _).trans ker)
    change ofFn 6 w.1=C (w.1 5)*anchorRadau at r
    have e3 : (0:K)+h A j3*0=normalProfileMap A w j3 := by rw [ker]; simp
    have e4 : (0:K)+h A j4*0=normalProfileMap A w j4 := by rw [ker]; simp
    have p := (interp w e3 e4).1
    change (ofFn 6 w.1).eval (2*d)=0 at p
    rw [r,eval_mul,eval_C] at p
    exact normal_coeff_forced_zero ha ho oneOff D w ker ((mul_eq_zero.mp p).resolve_right nz)
  have full : finrank K (treeSpace A 5)=10 := by
    by_contra ne
    have less : finrank K (treeSpace A 5)≤9 := by omega
    have rangeEq := Submodule.eq_of_le_of_finrank_le rangeSub (less.trans lower)
    have hR := LinearMap.finrank_range_of_inj (inject_by_radau (radau_ne rangeEq))
    rw [rangeEq,normal_coeff_rank] at hR
    exact ne hR
  have terminal := order9_rank_five_full ha ho full
  have gt : g A last=0 :=
    rank_five_full_terminal_defect ha ho full (zeroSpace_mono A (by decide) (qdef_mem A))
  have ht : h A last=0 := rank_five_full_terminal_defect ha ho full (h_in_grade_three A)
  have ct : nodes A last=1 := terminal.2.1
  have inj : Function.Injective (normalProfileMap A) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro w ker
    have r := wide_kernel_poly ha ho (w,0) ((wide_at_normal _).trans ker)
    change ofFn 6 w.1=C (w.1 5)*anchorRadau at r
    have p : (ofFn 6 w.1).eval 1=0 := by
      have E := (congrFun ker last).symm.trans (normal_profile_value w last)
      simpa only [ct,gt,ht,Pi.zero_apply,mul_zero,zero_mul,zero_add,add_zero] using E.symm
    rw [r,eval_mul,eval_C,anchorRadau_at_one] at p
    exact normal_coeff_forced_zero ha ho oneOff D w ker ((mul_eq_zero.mp p).resolve_right (by norm_num))
  have r10 := LinearMap.finrank_range_of_inj inj
  rw [normal_coeff_rank] at r10
  have rangeEq := Submodule.eq_of_le_of_finrank_le rangeSub (full.trans r10.symm).le
  refine ⟨full,rangeEq,radau_ne rangeEq,?_⟩
  have em : Pi.single last (1:K)∈LinearMap.range (normalProfileMap A) := by
    rw [rangeEq]
    exact terminal.2.2.1
  obtain ⟨w,E⟩ := em
  have e3 : (0:K)+h A j3*0=normalProfileMap A w j3 := by rw [E]; simp [last,j3]
  have e4 : (0:K)+h A j4*0=normalProfileMap A w j4 := by rw [E]; simp [last,j4]
  have p := (interp w e3 e4).1
  have q : (P w).eval 1=1 := by
    have e := (congrFun E last).symm.trans (normal_profile_value w last)
    simpa only [Pi.single_eq_same,ct,gt,ht,mul_zero,zero_mul,zero_add,add_zero] using e.symm
  intro same
  rw [same,q] at p
  exact one_ne_zero p

end RKCert.Paired.OneOff
