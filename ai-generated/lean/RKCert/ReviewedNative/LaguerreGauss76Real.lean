module

public import RKCert.ReviewedNative.LaguerreGauss76
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.FieldTheory.AlgebraicClosure

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

public section

/-! # The seven-stage witness over the real algebraic numbers

We construct the two positive square roots inside the relative algebraic
closure of ℚ in ℝ. The same certified tableau can be interpreted in either
field; its next-order discrepancy survives both maps. -/

namespace RKResearch.Certified.LaguerreGauss76

private theorem exists_positive_square_root {r : ℝ} (hr : 0 < r) :
    ∃ x : ℝ, 0 < x ∧ x^2 = r := by
  let S : Set ℝ := {x | 0 ≤ x ∧ x^2 ≤ r}
  have h0 : (0 : ℝ) ∈ S := ⟨le_rfl, by simpa using hr.le⟩
  have hs : S.Nonempty := ⟨0,h0⟩
  let M := r+1
  have hM : 0 < M := by dsimp [M]; linarith only [hr]
  have hMr : 0 ≤ M^2-r := by dsimp [M]; nlinarith only [hr, sq_nonneg r]
  have ub : BddAbove S := ⟨M, fun x hx => by
    change 0 ≤ x ∧ x^2 ≤ r at hx
    dsimp [M]; nlinarith only [hx.2, hr, sq_nonneg (x-1)]⟩
  let c := sSup S
  have hc : 0 ≤ c := le_csSup ub h0
  have hcd : 0 < c+M := add_pos_of_nonneg_of_pos hc hM
  let F (x : ℝ) := (M*x+r)/(x+M)
  have hle : c ≤ F c := by
    apply csSup_le hs
    intro x hx
    have hxc : x ≤ c := le_csSup ub hx
    change 0 ≤ x ∧ x^2 ≤ r at hx
    have hxd : 0 < x+M := add_pos_of_nonneg_of_pos hx.1 hM
    calc
      x ≤ F x := (le_div_iff₀ hxd).mpr (by nlinarith only [hx.2])
      _ ≤ F c := (div_le_div_iff₀ hxd hcd).mpr (by
        nlinarith only [mul_nonneg hMr (sub_nonneg.mpr hxc)])
  have hcSq : c^2 ≤ r := by nlinarith only [(le_div_iff₀ hcd).mp hle]
  have hF : F c ∈ S := by
    refine ⟨div_nonneg (add_nonneg (mul_nonneg hM.le hc) hr.le) hcd.le, ?_⟩
    have hfac : (F c)^2-r = (M^2-r)*(c^2-r)/(c+M)^2 := by
      dsimp only [F]
      field_simp
      ring
    have hs' : (M^2-r)*(c^2-r)/(c+M)^2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hMr
        (sub_nonpos.mpr hcSq)) (sq_nonneg _)
    linarith only [hfac,hs']
  have he : c^2 = r := by
    nlinarith only [hcSq, (div_le_iff₀ hcd).mp (le_csSup ub hF)]
  exact ⟨c, lt_of_le_of_ne hc (by intro e; rw [← e] at he; norm_num at he; linarith), he⟩

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

open Polynomial

/-- Positive algebraic roots select the same radical signs as the
Laguerre–Gauss construction. No sign test is needed to prove order. -/
theorem positive_algebraic_root (n : ℕ) (hn : 0 < n) :
    ∃ x : ℝₐ, 0 < (x : ℝ) ∧ x^2 = (n:ℝₐ) := by
  obtain ⟨x,hp,hx⟩ := exists_positive_square_root (r := (n : ℝ)) (by exact_mod_cast hn)
  have ha : IsAlgebraic ℚ x := by
    refine ⟨X^2 - C (n:ℚ), X_pow_sub_C_ne_zero (by decide) _, ?_⟩
    simp [hx]
  let xx : ℝₐ := ⟨x, mem_algebraicClosure_iff.mpr ha⟩
  refine ⟨xx, hp, (algebraMap ℝₐ ℝ).injective ?_⟩
  simp only [map_pow, map_natCast]
  exact hx

private theorem exact_exists_of_roots {K : Type*} [Field K] [CharZero K]
    {x y : K} (hx : x^2 = 2) (hy : y^2 = 15) :
    ∃ (A : Matrix (Fin 7) (Fin 7) K) (b : Fin 7 → K),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/2) ∧ (1/2:K) ≠ 0 ∧
        HasOrder A b 6 ∧ ¬ HasOrder A b 7 := by
  let f := specialize x y hx hy
  exact ⟨A.map f, f ∘ b, exact_map f⟩

/-- Seven physical stages, with a shared diagonal 1/2, have exactly order
six in the actual field of real algebraic numbers. -/
theorem exact_realAlgebraic :
    ∃ (A : Matrix (Fin 7) (Fin 7) ℝₐ) (b : Fin 7 → ℝₐ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/2) ∧ (1/2:ℝₐ) ≠ 0 ∧
        HasOrder A b 6 ∧ ¬ HasOrder A b 7 := by
  obtain ⟨x, -, hx⟩ := positive_algebraic_root 2 (by decide)
  obtain ⟨y, -, hy⟩ := positive_algebraic_root 15 (by decide)
  exact exact_exists_of_roots hx hy

theorem exact_real :
    ∃ (A : Matrix (Fin 7) (Fin 7) ℝ) (b : Fin 7 → ℝ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/2) ∧ (1/2:ℝ) ≠ 0 ∧
        HasOrder A b 6 ∧ ¬ HasOrder A b 7 := by
  obtain ⟨x, -, hx⟩ := exists_positive_square_root (r := 2) (by norm_num)
  obtain ⟨y, -, hy⟩ := exists_positive_square_root (r := 15) (by norm_num)
  exact exact_exists_of_roots hx hy

end RKResearch.Certified.LaguerreGauss76
