module

public import RKCert.ReviewedNative.ERK8CharElevenFourHead
public import RKCert.ReviewedNative.ERK8CharElevenFiveWeights

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Literal late reflected equations at the repeated tag
Both reflected rows are paid. The adjustment at the earlier repeat is
an identity in the original ten physical columns, not a stage merge. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven.FourOff

open RKResearch Polynomial OneOff ERKTaggedHorizon ERK8PaidField Reverse FourOffPhysical
open scoped Classical Matrix BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K} {P : K[X]} {dup k : Fin 10}

noncomputable def repeatDifference (A : Matrix (Fin 10) (Fin 10) K) (dup : Fin 10) : Fin 10→K :=
  mat A.transpose (contrast K dup 8)

theorem repeatDifference_apply (A : Matrix (Fin 10) (Fin 10) K) (dup j : Fin 10) :
    repeatDifference A dup j=A 8 j-A dup j := transpose_contrast_apply A dup 8 j

theorem repeatDifference_annih (M : Placement A b P dup k) :
    repeatDifference A dup∈annih (treeSpace A 4) := by
  rw [M.repeatAtEight.reverseSpace]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

theorem repeatDifference_eight_zero (ha : ∀ i j, i≤j → A i j=0)
    (R : RepeatAtEight A b dup) : repeatDifference A dup 8=0 := by
  rw [repeatDifference_apply,ha 8 8 le_rfl,ha dup 8 R.before.le,sub_self]

theorem reflected_J2_repeat (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (M : Placement A b P dup k) :
    ∃ ξ : K, reflectedStageRow A b 2 =
      reflectedClock A 8 • quadraticSeed A b+ξ • repeatDifference A dup := by
  let R := M.repeatAtEight
  have mem := reflectedStageRow_annih ho 4 2 (by decide)
  rw [R.reverseSpace,Submodule.mem_sup] at mem
  obtain ⟨u,um,v,vm,e⟩ := mem
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp um
  obtain ⟨ξ,rfl⟩ := Submodule.mem_span_singleton.mp vm
  have v8 := congrFun e 8
  change a * contrast K dup 8 8 + ξ * repeatDifference A dup 8=reflectedStageRow A b 2 8 at v8
  have s8 := reflected_row_tail (b:=b) ha (t:=8) (fun j h=>by
    have e9 : j=9 := by omega
    subst j
    simp [reflectedClock,M.rankData.clockNine]) (k:=8) le_rfl (m:=2) (by decide)
  rw [contrast_late (ne_of_lt R.before),repeatDifference_eight_zero ha R,s8,mul_one,mul_zero,add_zero] at v8
  refine ⟨ξ,?_⟩
  rw [R.quad,smul_smul]
  have aeq : a=reflectedClock A 8 * (-(b 8*(reflectedClock A 8)^2)) := by
    rw [v8]
    ring
  rw [←aeq]
  exact e.symm

theorem reflected_clock_repeat (R : RepeatAtEight A b dup) :
    reflectedClock A dup=reflectedClock A 8 := by
  simp only [reflectedClock,Pi.sub_apply,Pi.one_apply,R.same.1]

/-- The actual mass of an early clean tag. The repeat may be either
quadratic clean stage, an earlier clean tag, or an off tag. -/
theorem cleanMass_early_with_repeat (M : Placement A b P dup k) (w : Fin 10→K)
    {j : Fin 10} (j8 : j < 8) (gj : g A j=0) (cj : nodes A j≠1) :
    cleanMass A w (nodes A j)=w j+(if dup=j then w 8 else 0) := by
  let R := M.repeatAtEight
  unfold cleanMass
  have hj8 : j≠8 := ne_of_lt j8
  rw [FiveOff.sum_pair_of_support hj8]
  · simp only [gj,true_and]
    by_cases dj : dup=j
    · subst dup
      simp [R.same.2.mp gj,←R.same.1]
    · have n : ¬ (g A 8=0 ∧ nodes A 8=nodes A j) := fun u =>
        dj ((R.unique j8 ⟨u.2.symm,iff_of_true gj u.1⟩).1.symm)
      simp [n,dj]
  · intro l lj l8
    have n : ¬ (g A l=0 ∧ nodes A l=nodes A j) := by
      intro u
      by_cases l9 : l=9
      · exact cj (u.2.symm.trans (l9 ▸ M.rankData.clockNine))
      have llt : l < 8 := by omega
      rcases lt_or_gt_of_ne lj with lt|lt
      · exact hj8 (R.unique lt ⟨u.2,iff_of_true u.1 gj⟩).2
      · exact l8 (R.unique lt ⟨u.2.symm,iff_of_true gj u.1⟩).2
    simp [n]

theorem reflected_row_at_seven (ha : ∀ i j, i≤j → A i j=0)
    (c9 : nodes A 9=1) (m : ℕ) (hm : 0<m) :
    reflectedStageRow A b m 7 =
      (((m+1:ℕ):K))*(b 8*(reflectedClock A 8)^m*A 8 7)-
      b 7*(reflectedClock A 7)^(m+1) := by
  change (((m+1:ℕ):K))*(∑ i : Fin 10, A i 7*(b i*(reflectedClock A i)^m))-_ = _
  rw [Finset.sum_eq_single 8]
  · ring
  · intro i _ i8
    by_cases i9 : i=9
    · subst i
      simp [reflectedClock,c9,zero_pow (ne_of_gt hm)]
    have rh : i≤7 := by omega
    rw [ha i 7 rh,zero_mul]
  · simp

theorem reflected_row_at_six (ha : ∀ i j, i≤j → A i j=0)
    (c9 : nodes A 9=1) (m : ℕ) (hm : 0<m) :
    reflectedStageRow A b m 6 =
      (((m+1:ℕ):K))*(b 7*(reflectedClock A 7)^m*A 7 6+b 8*(reflectedClock A 8)^m*A 8 6)-
      b 6*(reflectedClock A 6)^(m+1) := by
  change (((m+1:ℕ):K))*(∑ i : Fin 10, A i 6*(b i*(reflectedClock A i)^m))-_ = _
  rw [FiveOff.sum_pair_of_support (by decide : (7:Fin 10)≠8)]
  · ring
  · intro i i7 i8
    by_cases i9 : i=9
    · subst i
      simp [reflectedClock,c9,zero_pow (ne_of_gt hm)]
    have rh : i≤6 := by omega
    rw [ha i 6 rh,zero_mul]

theorem late_reflected_repeat_equations
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (M : Placement A b P dup k)
    (c61 : nodes A 6≠1) (c71 : nodes A 7≠1) :
    let y := reflectedClock A
    let W₆ := cleanMass A b (nodes A 6)
    let W₇ := cleanMass A b (nodes A 7)
    let Δ := repeatDifference A dup
    ∃ ξ : K,
      2*(b 8*y 8)*Δ 7=W₇*(y 7)^2 ∧
      (3*b 8*(y 8)^2-ξ)*Δ 7=W₇*(y 7)^3 ∧
      2*(W₇*y 7*A 7 6+b 8*y 8*Δ 6)=W₆*(y 6)^2 ∧
      3*(W₇*(y 7)^2*A 7 6)+(3*b 8*(y 8)^2-ξ)*Δ 6=W₆*(y 6)^3 := by
  dsimp only
  let R := M.repeatAtEight
  obtain ⟨ξ,J₂⟩ := reflected_J2_repeat ha ho M
  have j2 (i : Fin 10) : reflectedStageRow A b 2 i=
      reflectedClock A 8*quadraticSeed A b i+ξ*repeatDifference A dup i := congrFun J₂ i
  have e1 (i : Fin 10) (i8 : i≠8) :
      quadraticSeed A b i=(if dup=i then b 8*(reflectedClock A 8)^2 else 0) := by
    have t := congrFun R.quad i
    change quadraticSeed A b i = (-(b 8*(reflectedClock A 8)^2))*contrast K dup 8 i at t
    by_cases eq : dup=i
    · subst i
      rw [contrast_early (ne_of_lt R.before)] at t
      simp only [ite_true]
      linear_combination t
    · rw [contrast_other (Ne.symm eq) i8,mul_zero] at t
      simpa [eq] using t
  have b₆ := cleanMass_early_with_repeat M b (j:=6) (by decide) M.cleanSix c61
  have b₇ := cleanMass_early_with_repeat M b (j:=7) (by decide) M.cleanSeven c71
  have d7 : A 8 7=repeatDifference A dup 7 := by
    rw [repeatDifference_apply,ha dup 7 (by have u := R.before; omega),sub_zero]
  have yrep : reflectedClock A dup=reflectedClock A 8 := reflected_clock_repeat R
  have exp17 := reflected_row_at_seven (b:=b) ha M.rankData.clockNine 1 (by decide)
  have exp27 := reflected_row_at_seven (b:=b) ha M.rankData.clockNine 2 (by decide)
  have exp16 := reflected_row_at_six (b:=b) ha M.rankData.clockNine 1 (by decide)
  have exp26 := reflected_row_at_six (b:=b) ha M.rankData.clockNine 2 (by decide)
  simp only [Nat.reduceAdd,Nat.cast_ofNat,pow_one] at exp17 exp27 exp16 exp26
  change quadraticSeed A b 7=_ at exp17
  change quadraticSeed A b 6=_ at exp16
  have H7 := j2 7
  have H6 := j2 6
  rw [e1 7 (by decide)] at exp17 H7
  rw [e1 6 (by decide)] at exp16 H6
  rw [d7] at exp17 exp27
  have d6 : A 8 6=repeatDifference A dup 6+(if dup=7 then A 7 6 else 0) := by
    rw [repeatDifference_apply]
    by_cases eq : dup=7
    · simp [eq]
    · have u := R.before
      rw [ite_eq_right eq,ha dup 6 (by omega),sub_zero,add_zero]
  rw [d6] at exp16 exp26
  refine ⟨ξ, ?_, ?_, ?_, ?_⟩
  · by_cases d : dup=7
    · have y7 : reflectedClock A 7=reflectedClock A 8 := d ▸ yrep
      rw [b₇,ite_eq_left d,y7]
      rw [ite_eq_left d,y7] at exp17
      linear_combination -exp17
    · rw [b₇,ite_eq_right d]
      rw [ite_eq_right d] at exp17
      linear_combination -exp17
  · by_cases d : dup=7
    · have y7 : reflectedClock A 7=reflectedClock A 8 := d ▸ yrep
      rw [b₇,ite_eq_left d,y7]
      rw [ite_eq_left d] at H7
      rw [y7] at exp27
      linear_combination H7-exp27
    · rw [b₇,ite_eq_right d]
      rw [ite_eq_right d] at H7
      linear_combination H7-exp27
  · by_cases d : dup=7
    · have n : dup≠6 := fun u=>by omega
      have y7 : reflectedClock A 7=reflectedClock A 8 := d ▸ yrep
      rw [b₆,b₇,ite_eq_left d,ite_eq_right n,y7]
      rw [ite_eq_left d,ite_eq_right n,y7] at exp16
      linear_combination -exp16
    · rw [b₆,b₇,ite_eq_right d]
      rw [ite_eq_right d] at exp16
      by_cases e : dup=6
      · have y6 : reflectedClock A 6=reflectedClock A 8 := e ▸ yrep
        rw [ite_eq_left e,y6] at exp16 ⊢
        linear_combination -exp16
      · rw [ite_eq_right e] at exp16 ⊢
        linear_combination -exp16
  · by_cases d : dup=7
    · have n : dup≠6 := fun u=>by omega
      have y7 : reflectedClock A 7=reflectedClock A 8 := d ▸ yrep
      rw [b₆,b₇,ite_eq_left d,ite_eq_right n,y7]
      rw [ite_eq_left d,y7] at exp26
      rw [ite_eq_right n] at H6
      linear_combination H6-exp26
    · rw [b₆,b₇,ite_eq_right d]
      rw [ite_eq_right d] at exp26
      by_cases e : dup=6
      · have y6 : reflectedClock A 6=reflectedClock A 8 := e ▸ yrep
        rw [ite_eq_left e,y6]
        rw [ite_eq_left e] at H6
        rw [y6] at exp26
        linear_combination H6-exp26
      · rw [ite_eq_right e] at H6 ⊢
        linear_combination H6-exp26

end RKResearch.Certified.Graded.ERK8CharEleven.FourOff

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FourOff.late_reflected_repeat_equations
