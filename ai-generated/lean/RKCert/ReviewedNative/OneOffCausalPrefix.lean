module

public import RKCert.ReviewedNative.OneOffFifth
public import RKCert.ReviewedNative.OrderNineCausalInterpolation

@[expose] public section

/-! # Independent physical prefix rows from paid grade-four tests -/
namespace RKResearch.Certified.Graded.OneOff
open RKResearch Module Reverse
open scoped Classical Matrix

variable {K : Type*} [Field K] [CharZero K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}

omit [CharZero K] in
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

theorem order9_first_five_independent {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 9 A b)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j)
    (F : FirstFour A a d (by decide)) :
    IndependentBefore (treeSpace A 4) (5:Fin 12) := by
  let r : Fin 12 := 4
  let V : Fin 12 → K := deltaH A d-(d*(a*d^2)) • chartSelector A a d 3
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have C : FirstChartBefore A a d r := firstChartBefore_four (by decide) rfl F
  have ind := first_four_independent an dn C
  have vm : V∈treeSpace A 4 := (treeSpace A 4).sub_mem
    (zeroSpace_le_treeSpace A 4 (deltaH_in_grade_four A d))
    ((treeSpace A 4).smul_mem _ (treeSpace_mono A (by decide : 2≤4) (chart_selector_mem A a d 3)))
  have van (u : Fin 12) (ur : u < r) : V u=0 := by
    obtain ⟨l,ll,cu,gu⟩ := C u ur
    have fu := F.features l
    rw [(Fin.ext ll : Fin.castLE (by decide : 4≤12) l=u)] at fu
    have sel := chart_selector_nodes an dn cu gu 3
    simp only [V,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,deltaH_apply,
      cu,fu.2.2,sel]
    clear sel fu gu cu ll ur
    fin_cases l <;> norm_num [chartNode,chartH]
    ring
  have f4 := order9_fifth_feature ha ho D F
  have sel : chartSelector A a d 3 r=1 := by
    have cn : nodes A r=chartNode a d 3 := by simpa [chartNode] using f4.1
    have cg : g A r=chartDefect a 3 := by simpa [chartDefect] using f4.2.1
    simpa using chart_selector_nodes an dn cn cg 3
  have cr : nodes A r=2*d := f4.1
  have vn : V r≠0 := by
    have ve : V r=d*(h A r-a*d^2) := by
      simp only [V,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,deltaH_apply,cr,sel,mul_one]
      ring
    rw [ve]
    exact mul_ne_zero dn (sub_ne_zero.mpr f4.2.2)
  exact extend_independent_before (j:=r) (r:=(5:Fin 12)) rfl ind vm van vn

end RKResearch.Certified.Graded.OneOff
