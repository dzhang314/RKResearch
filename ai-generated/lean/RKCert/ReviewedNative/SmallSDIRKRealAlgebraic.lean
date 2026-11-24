module

public import RKCert.ReviewedNative.SmallSDIRK
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.FieldTheory.AlgebraicClosure

import Mathlib.Tactic.Linarith

public section

/-!
# Real algebraic instances of the classical small SDIRKs

Exact rational brackets identify the positive quadratic root and the root
of the cubic larger than one. The root proof uses real completeness and a
factor bound on the bracket, so no floating approximation or order
condition is assumed. The witnesses then live in Mathlib's actual
relative algebraic closure of the rationals in the reals.
-/

namespace RKResearch.Certified

/-- The sign-change principle for functions with a proved Lipschitz estimate
on a compact interval. Only real order-completeness is needed here. -/
private theorem exists_root_of_bound {a b M : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hM : 0 < M) (ha : f a < 0) (hb : 0 < f b)
    (hbound : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ M * |x - y|) :
    ∃ x ∈ Set.Ioo a b, f x = 0 := by
  let S := {x : ℝ | x ∈ Set.Icc a b ∧ f x ≤ 0}
  have haS : a ∈ S := ⟨⟨le_rfl, hab.le⟩, ha.le⟩
  have hs : S.Nonempty := ⟨a, haS⟩
  have hB : BddAbove S := ⟨b, fun _ hx => hx.1.2⟩
  let c := sSup S
  have hc : c ∈ Set.Icc a b := ⟨le_csSup hB haS, csSup_le hs fun _ hx => hx.1.2⟩
  have hfc : f c ≤ 0 := by
    by_contra! hn
    let d := f c / M
    have hd : 0 < d := div_pos hn hM
    obtain ⟨x, hx, hxc⟩ := exists_lt_of_lt_csSup hs (sub_lt_self c hd)
    have hxle : x ≤ c := le_csSup hB hx
    have hclose : |x-c| < d := by
      rw [abs_of_nonpos (sub_nonpos.mpr hxle)]
      linarith only [hxc]
    have hscaled := (lt_div_iff₀ hM).mp hclose
    have hfx := (abs_le.mp (hbound x hx.1 c hc)).1
    rw [mul_comm M] at hfx
    linarith only [hx.2, hfx, hscaled]
  have hcb : c < b := lt_of_le_of_ne hc.2 (by
    intro h
    rw [h] at hfc
    exact hb.not_ge hfc)
  have hfc' : 0 ≤ f c := by
    by_contra! hn
    let d := min ((b-c)/2) (-f c/M)
    have hd : 0 < d := lt_min (by linarith only [hcb]) (div_pos (neg_pos.mpr hn) hM)
    have hd' : d ≤ (b-c)/2 := min_le_left _ _
    have hd'' : d ≤ -f c/M := min_le_right _ _
    let x := c+d
    have hcx : c < x := lt_add_of_pos_right _ hd
    have hx : x ∈ Set.Icc a b := ⟨hc.1.trans hcx.le, by dsimp [x]; linarith only [hcb, hd']⟩
    have hclose : |x-c| = d := by
      rw [show x-c = d by dsimp [x]; ring, abs_of_pos hd]
    have hfx := (abs_le.mp (hbound x hx c hc)).2
    rw [hclose, mul_comm M] at hfx
    have hscaled := (le_div_iff₀ hM).mp hd''
    have hxS : x ∈ S := ⟨hx, by linarith only [hfx, hscaled]⟩
    exact hcx.not_ge (le_csSup hB hxS)
  have hzero : f c = 0 := le_antisymm hfc hfc'
  have hac : a < c := lt_of_le_of_ne hc.1 (by
    intro h
    rw [← h] at hzero
    exact ha.ne hzero)
  exact ⟨c, ⟨hac, hcb⟩, hzero⟩

namespace NorsettCrouzeix23

/-- The rational bracket isolates the larger root corresponding to the
published two-stage method. -/
theorem real_root : ∃! x : ℝ, x ∈ Set.Ioo (1/2) (2/3) ∧ x^2 - 1/3 = 0 := by
  let f : ℝ → ℝ := fun x => x^2-1/3
  have hb₁ : f (1/2) = -1/12 := by norm_num [f]
  have hb₂ : f (2/3) = 1/9 := by norm_num [f]
  obtain ⟨x, hx, hx0⟩ := exists_root_of_bound (M := 2) (f := f)
    (a := 1/2) (b := 2/3) (by norm_num) (by norm_num)
    (by rw [hb₁]; norm_num) (by rw [hb₂]; norm_num) (by
      intro x hx y hy
      have hsum : |x+y| ≤ 2 := abs_le.mpr
        ⟨by linarith only [hx.1, hy.1], by linarith only [hx.2, hy.2]⟩
      rw [show f x-f y = (x+y)*(x-y) by dsimp [f]; ring, abs_mul]
      exact mul_le_mul_of_nonneg_right hsum (abs_nonneg _))
  refine ⟨x, ⟨hx, hx0⟩, ?_⟩
  intro y hy
  have hprod : (y-x)*(y+x) = 0 := by
    dsimp [f] at hx0
    linear_combination hy.2 - hx0
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right
    (by linarith only [hy.1.1, hx.1]))

end NorsettCrouzeix23

namespace Crouzeix34

/-- The rational bracket isolates the cubic root larger than one that
corresponds to the published three-stage method. -/
theorem real_root : ∃! x : ℝ, x ∈ Set.Ioo 1 (6/5) ∧ x^3-x-1/3 = 0 := by
  let f : ℝ → ℝ := fun x => x^3-x-1/3
  have hb₁ : f 1 = -1/3 := by norm_num [f]
  have hb₂ : f (6/5) = 73/375 := by norm_num [f]
  obtain ⟨x, hx, hx0⟩ := exists_root_of_bound (M := 5) (f := f)
    (a := 1) (b := 6/5) (by norm_num) (by norm_num)
    (by rw [hb₁]; norm_num) (by rw [hb₂]; norm_num) (by
      intro x hx y hy
      have hx0 : 0 ≤ x := (show (0 : ℝ) ≤ 1 by norm_num).trans hx.1
      have hy0 : 0 ≤ y := (show (0 : ℝ) ≤ 1 by norm_num).trans hy.1
      have hm : x*y ≤ (6/5)^2 := by
        rw [pow_two]
        exact mul_le_mul hx.2 hy.2 hy0 (by norm_num)
      have hs : |x^2+x*y+y^2-1| ≤ 5 := abs_le.mpr
        ⟨by nlinarith only [sq_nonneg x, sq_nonneg y, mul_nonneg hx0 hy0],
          by nlinarith only [hm, mul_le_mul hx.2 hx.2 hx0 (by norm_num),
            mul_le_mul hy.2 hy.2 hy0 (by norm_num)]⟩
      rw [show f x-f y = (x^2+x*y+y^2-1)*(x-y) by dsimp [f]; ring, abs_mul]
      exact mul_le_mul_of_nonneg_right hs (abs_nonneg _))
  refine ⟨x, ⟨hx, hx0⟩, ?_⟩
  intro y hy
  have hprod : (y-x)*(y^2+y*x+x^2-1) = 0 := by
    dsimp [f] at hx0
    linear_combination hy.2 - hx0
  have hpos : 0 < y^2+y*x+x^2-1 := by
    nlinarith only [hy.1.1, hx.1, sq_nonneg (y-1), sq_nonneg (x-1),
      mul_nonneg (show 0 ≤ y by linarith only [hy.1.1]) (show 0 ≤ x by linarith only [hx.1])]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hpos.ne')

end Crouzeix34

open Polynomial

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

theorem NorsettCrouzeix23.algebraic_root :
    ∃ x : ℝₐ, (x : ℝ) ∈ Set.Ioo (1/2) (2/3) ∧ x^2-1/3 = 0 := by
  obtain ⟨x, ⟨hI, hx⟩, -⟩ := real_root
  have hxA : IsAlgebraic ℚ x := by
    refine ⟨X^2 - C (1/3), X_pow_sub_C_ne_zero (by decide) _, ?_⟩
    simpa [Rat.cast_div] using hx
  let xx : ℝₐ := ⟨x, mem_algebraicClosure_iff.mpr hxA⟩
  refine ⟨xx, hI, (algebraMap ℝₐ ℝ).injective ?_⟩
  simp only [map_sub, map_pow, map_div₀, map_one, map_ofNat, map_zero]
  exact hx

theorem Crouzeix34.algebraic_root :
    ∃ x : ℝₐ, (x : ℝ) ∈ Set.Ioo 1 (6/5) ∧ x^3-x-1/3 = 0 := by
  obtain ⟨x, ⟨hI, hx⟩, -⟩ := real_root
  have hxA : IsAlgebraic ℚ x := by
    refine ⟨X^3-X-C (1/3), ?_, ?_⟩
    · intro h
      have hc := congrArg (fun p : ℚ[X] => p.coeff 3) h
      norm_num [coeff_sub, coeff_X_pow, coeff_X, coeff_C] at hc
    · simpa [Rat.cast_div] using hx
  let xx : ℝₐ := ⟨x, mem_algebraicClosure_iff.mpr hxA⟩
  refine ⟨xx, hI, (algebraMap ℝₐ ℝ).injective ?_⟩
  simp only [map_sub, map_pow, map_div₀, map_one, map_ofNat, map_zero]
  exact hx

theorem exists_strictSDIRK_exact_three_realAlgebraic :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℝₐ) (b : Fin 2 → ℝₐ) (γ : ℝₐ),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder A b 3 ∧ ¬ HasOrder A b 4 := by
  obtain ⟨x, -, hx⟩ := NorsettCrouzeix23.algebraic_root
  exact ⟨NorsettCrouzeix23.A x, NorsettCrouzeix23.b, smallSDIRKGamma x,
    NorsettCrouzeix23.lowerTriangular x, NorsettCrouzeix23.diagonal x,
    NorsettCrouzeix23.diagonal_ne_zero hx, NorsettCrouzeix23.order_three hx,
    NorsettCrouzeix23.not_order_four hx⟩

theorem exists_strictSDIRK_exact_four_realAlgebraic :
    ∃ (A : Matrix (Fin 3) (Fin 3) ℝₐ) (b : Fin 3 → ℝₐ) (γ : ℝₐ),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder A b 4 ∧ ¬ HasOrder A b 5 := by
  obtain ⟨x, -, hx⟩ := Crouzeix34.algebraic_root
  exact ⟨Crouzeix34.A x, Crouzeix34.b x, smallSDIRKGamma x,
    Crouzeix34.lowerTriangular x, Crouzeix34.diagonal x, Crouzeix34.diagonal_ne_zero hx,
    Crouzeix34.order_four hx, Crouzeix34.not_order_five hx⟩

end RKResearch.Certified
