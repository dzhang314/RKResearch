module

public import RKCert.ReviewedNative.CooperSayfy55
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.FieldTheory.AlgebraicClosure

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

public section

/-!
# The published Cooper–Sayfy tableau over the real algebraic numbers

The root between 2 and 3 selects the original (not its conjugate) tableau.
This module uses just real completeness and the relative algebraic closure;
no floating-point or rational approximation enters the existence proof.
-/

namespace RKResearch.Certified

namespace CooperSayfy55

/-- The positive root is uniquely characterized by its rational bracket.
For existence, `F(y) = (3y+6)/(y+3)` pushes any nonnegative subroot
upwards to another subroot. Monotonicity forces the supremum to be fixed. -/
theorem real_root : ∃! x : ℝ, x ∈ Set.Ioo 2 3 ∧ x^2 = 6 := by
  let S : Set ℝ := {y | 0 ≤ y ∧ y^2 ≤ 6}
  let c := sSup S
  have h2 : (2 : ℝ) ∈ S := by norm_num [S]
  have hs : S.Nonempty := ⟨2, h2⟩
  have hup : ∀ y ∈ S, y ≤ 3 := by
    intro y hy
    nlinarith only [hy.2, sq_nonneg (y-3)]
  have hb : BddAbove S := ⟨3, hup⟩
  have hl : 2 ≤ c := le_csSup hb h2
  have hr : c ≤ 3 := csSup_le hs hup
  let F (y : ℝ) := (3*y+6)/(y+3)
  have hcden : 0 < c+3 := by linarith only [hl]
  have hle : c ≤ F c := by
    apply csSup_le hs
    intro y hy
    have hden : 0 < y+3 := by linarith only [hy.1]
    have hyc : y ≤ c := le_csSup hb hy
    calc
      y ≤ F y := (le_div_iff₀ hden).mpr (by nlinarith only [hy.2])
      _ ≤ F c := (div_le_div_iff₀ hden hcden).mpr (by nlinarith only [hyc])
  have hcsq : c^2 ≤ 6 := by
    nlinarith only [(le_div_iff₀ hcden).mp hle]
  have hF : F c ∈ S := by
    refine ⟨div_nonneg (by linarith only [hl]) hcden.le, ?_⟩
    have hfac : (F c)^2 - 6 = 3*(c^2-6)/(c+3)^2 := by
      dsimp only [F]
      field_simp
      ring
    have hsign : 3*(c^2-6)/(c+3)^2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith only [hcsq]) (sq_nonneg _)
    linarith only [hfac, hsign]
  have he : c^2 = 6 := by
    have hge : F c ≤ c := le_csSup hb hF
    nlinarith only [(div_le_iff₀ hcden).mp hge, hcsq]
  have hi : c ∈ Set.Ioo 2 3 :=
    ⟨lt_of_le_of_ne hl (by rintro h; rw [← h] at he; norm_num at he),
      lt_of_le_of_ne hr (by rintro h; rw [h] at he; norm_num at he)⟩
  refine ⟨c, ⟨hi, he⟩, ?_⟩
  intro y hy
  have hz : (y-c)*(y+c) = 0 := by nlinarith only [hy.2, he]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (by linarith only [hy.1.1, hl]))

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

open Polynomial

/-- The bracketed root lives in Mathlib's actual field of real algebraic numbers. -/
theorem algebraic_root : ∃ x : ℝₐ, (x : ℝ) ∈ Set.Ioo 2 3 ∧ x^2 = 6 := by
  obtain ⟨x, ⟨hi, hx⟩, -⟩ := real_root
  have ha : IsAlgebraic ℚ x := by
    refine ⟨X^2 - C 6, X_pow_sub_C_ne_zero (by decide) _, ?_⟩
    simp [hx]
  let xx : ℝₐ := ⟨x, mem_algebraicClosure_iff.mpr ha⟩
  refine ⟨xx, hi, (algebraMap ℝₐ ℝ).injective ?_⟩
  simp only [map_pow, map_ofNat]
  exact hx

end CooperSayfy55

open CooperSayfy55

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

/-- The classical five-stage strict SDIRK attains exactly order five over
the real algebraic numbers. No claim of A-stability or optimality is required. -/
theorem exists_strictSDIRK_exact_five_realAlgebraic :
    ∃ (A : Matrix (Fin 5) (Fin 5) ℝₐ) (b : Fin 5 → ℝₐ) (γ : ℝₐ),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder 5 A b ∧ ¬ HasOrder 6 A b := by
  obtain ⟨x, -, hx⟩ := algebraic_root
  let f := specialize x hx
  exact ⟨A.map f, f ∘ b, f gamma, specialized_exact x hx⟩

/-- The corresponding concrete bound over the real numbers. -/
theorem exists_strictSDIRK_exact_five_real :
    ∃ (A : Matrix (Fin 5) (Fin 5) ℝ) (b : Fin 5 → ℝ) (γ : ℝ),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder 5 A b ∧ ¬ HasOrder 6 A b := by
  obtain ⟨x, ⟨-, hx⟩, -⟩ := real_root
  let f := specialize x hx
  exact ⟨A.map f, f ∘ b, f gamma, specialized_exact x hx⟩

end RKResearch.Certified
