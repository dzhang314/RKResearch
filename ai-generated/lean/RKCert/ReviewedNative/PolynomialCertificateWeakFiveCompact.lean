module

public import RKCert.ReviewedNative.CubicJacobiPencilSix
public import RKCert.ReviewedNative.PolynomialCertificatePencilResidue
public import RKCert.ReviewedNative.PolynomialCertificateWronskianPositive
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCuts

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Compactification of the *actual* split Jacobi pencil

The chart square includes all eight-simple-interior-root pencils, up to the
displayed reflection. The lower parameter bound uses no analytic root counts,
critical-point isolation, or IVT in the given ordered field. -/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.JacobiSix
open scoped BigOperators Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

noncomputable def unitPencil (d κ : K) : K[X] := (X - C d) * J7 K - C κ * J6 K

private noncomputable def J6expr : K[X] := C (1/429 : K) *
  (1 - 27*X + 225*X^2 - 825*X^3 + 1485*X^4 - 1287*X^5 + 429*X^6)

private noncomputable def J7expr : K[X] := C (1/1430 : K) *
  (-1 + 35*X - 385*X^2 + 1925*X^3 - 5005*X^4 + 7007*X^5 - 5005*X^6 + 1430*X^7)

private theorem j6expr_eq : J6 K = J6expr := by
  apply Polynomial.funext
  intro x
  rw [J6_eval_centered]
  norm_num [J6expr] <;> ring

private theorem j7expr_eq : J7 K = J7expr := by
  apply Polynomial.funext
  intro x
  rw [J7_eval_centered]
  norm_num [J7expr] <;> ring

/-- In centered coordinates the scale is 715². In the physical coordinate
the additional factor is 4096, since the two monic polynomials have degrees 6 and 7. -/
theorem jacobi_wronskian_identity (x : K) :
    (715 : K)^2 * 4096 * (3*((J6 K).eval x * (J7 K).derivative.eval x -
      (J6 K).derivative.eval x * (J7 K).eval x) - 80*((J7 K).eval x)^2) =
    25*(1-(2*x-1)^2) * wronskianH ((2*x-1)^2) := by
  rw [j6expr_eq, j7expr_eq]
  norm_num [J6expr, J7expr, wronskianH, derivative_mul, derivative_sub, derivative_add,
    derivative_pow] <;> ring

theorem jacobi_wronskian_bound {x : K} (hx : x ∈ Set.Icc 0 1) :
    80*((J7 K).eval x)^2 ≤ 3*((J6 K).eval x * (J7 K).derivative.eval x -
      (J6 K).derivative.eval x * (J7 K).eval x) := by
  have left : 0 ≤ (2*x-1)^2 := sq_nonneg _
  have right : (2*x-1)^2 ≤ 1 := by nlinarith only [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hh := wronskianH_nonneg (show (2*x-1)^2 ∈ Set.Icc 0 1 from ⟨left, right⟩)
  have pos : 0 ≤ 25*(1-(2*x-1)^2) * wronskianH ((2*x-1)^2) :=
    mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr right)) hh
  have eqn := jacobi_wronskian_identity x
  linarith only [eqn, pos]

theorem unitPencil_monic_degree (d κ : K) : (unitPencil d κ).Monic ∧ (unitPencil d κ).natDegree = 8 := by
  have hi : ((X-C d)*J7 K).natDegree = 8 := by
    rw [natDegree_mul (X_sub_C_ne_zero _) (J7_monic K).ne_zero, natDegree_X_sub_C, J7_natDegree]
  have small : (C κ * J6 K).natDegree < ((X - C d)*J7 K).natDegree := by
    rw [hi]
    exact (natDegree_C_mul_le _ _).trans_lt (by rw [J6_natDegree]; decide)
  exact ⟨((monic_X_sub_C d).mul (J7_monic K)).sub_of_left (degree_lt_degree small),
    (natDegree_sub_eq_left_of_natDegree_lt small).trans hi⟩

/-- Sharper than a bound from the elementary symmetric coefficients:
the lower cutoff is exactly the one used by the published square. -/
theorem unitPencil_parameter_bounds {d κ : K} {β : Fin 8 → K}
    (inj : Function.Injective β) (unit : ∀ i, β i ∈ Set.Ioo 0 1)
    (roots : ∀ i, (unitPencil d κ).IsRoot (β i)) :
    -(3/80 : K) < κ ∧ (10/3 : K)*κ < d ∧ d < 1-(10/3 : K)*κ := by
  classical
  obtain ⟨mon, deg⟩ := unitPencil_monic_degree d κ
  have d8 : (unitPencil d κ).degree = (Finset.univ : Finset (Fin 8)).card := by
    rw [degree_eq_natDegree mon.ne_zero, deg]
    simp
  have low : (J7 K).degree < (Finset.univ : Finset (Fin 8)).card := by
    rw [degree_eq_natDegree (J7_monic K).ne_zero, J7_natDegree]
    norm_num
  have top : 0 < (J7 K).coeff ((Finset.univ : Finset (Fin 8)).card - 1) := by
    simpa only [Finset.card_univ, Fintype.card_fin, show 8-1=7 by decide, J7_coeff_top] using
      (zero_lt_one : (0 : K) < 1)
  have lower := pencil_lower_of_wronskian Finset.univ inj.injOn (J7 K) (J6 K) d κ 3 80
    (by norm_num) (by norm_num) mon d8 (fun i _ => roots i) low top
    (fun i _ => jacobi_wronskian_bound ⟨(unit i).1.le, (unit i).2.le⟩)
  have nodal := root_polynomial_eq_nodal Finset.univ inj.injOn mon d8 (fun i _ => roots i)
  have e0 : 0 < (unitPencil d κ).eval 0 := by
    calc
      0 < ∏ i : Fin 8, β i := Finset.prod_pos (fun i _ => (unit i).1)
      _ = (unitPencil d κ).eval 0 := by
        rw [nodal, Lagrange.eval_nodal]
        simp [Finset.prod_neg] <;> norm_num
  have e1 : 0 < (unitPencil d κ).eval 1 := by
    rw [nodal, Lagrange.eval_nodal]
    exact Finset.prod_pos (fun i _ => sub_pos.mpr (unit i).2)
  norm_num [unitPencil, J6_eval_centered, J7_eval_centered] at e0 e1
  exact ⟨lower, by linarith only [e0], by linarith only [e1]⟩

private theorem reflect_unitPencil (d κ x : K) :
    (unitPencil (1-d) κ).eval (1-x) = (unitPencil d κ).eval x := by
  simp [unitPencil, J6_eval_centered, J7_eval_centered]
  <;> ring

private theorem centered_root_of_params {δ κ s t x : K}
    (p1 : 15*s-3 = 80*κ) (p2 : 15*(1-s)*t = 12*(1-2*δ))
    (rt : (unitPencil δ κ).IsRoot x) :
    (centeredPolynomial s t).IsRoot (2*x-1) := by
  change (unitPencil δ κ).eval x = 0 at rt
  simp only [unitPencil, eval_sub, eval_mul, eval_X, eval_C, J6_eval_centered, J7_eval_centered] at rt
  simp only [IsRoot, centeredPolynomial, eval_add, eval_sub, eval_mul, eval_X, eval_C, p1, p2,
    sixthColumn, seventhColumn, eval_pow]
  norm_num
  linear_combination (2196480 : K) * rt

/-- A true compact chart with only a reflection disjunction, over the
given ordered field containing the sites. No membership conditions on any root
of P7, no analytically chosen critical points and no parameter guesses. -/
theorem exists_compact_chart_or_reflection {d κ : K} {β : Fin 8 → K}
    (inj : Function.Injective β) (unit : ∀ i, β i ∈ Set.Ioo 0 1)
    (roots : ∀ i, (unitPencil d κ).IsRoot (β i)) :
    ∃ s ∈ Set.Icc (0 : K) 1, ∃ t ∈ Set.Icc (0 : K) 1,
      (∀ i, (centeredPolynomial s t).IsRoot (2*β i-1)) ∨
      (∀ i, (centeredPolynomial s t).IsRoot (2*(1-β i)-1)) := by
  obtain ⟨low, dlow, dhi⟩ := unitPencil_parameter_bounds inj unit roots
  let δ := if d ≤ 1/2 then d else 1-d
  have δhi : δ ≤ 1/2 := by
    dsimp only [δ]
    split <;> rename_i h <;> linarith
  have δlo : (10/3 : K)*κ < δ := by
    dsimp only [δ]
    split
    · exact dlow
    · linarith only [dhi]
  let s := (80*κ+3)/15
  have s0 : 0 < s := by dsimp [s]; linarith only [low]
  have s1 : s < 1 := by dsimp [s]; linarith only [dlow, dhi]
  let t := 4*(1-2*δ)/(5*(1-s))
  have den : 0 < 5*(1-s) := mul_pos (by norm_num) (sub_pos.mpr s1)
  have t0 : 0 ≤ t := div_nonneg (by linarith only [δhi]) den.le
  have t1 : t ≤ 1 := by
    apply (div_le_iff₀ den).mpr
    dsimp only [s]
    linarith only [δlo]
  have p1 : 15*s-3 = 80*κ := by dsimp only [s]; ring
  have p2 : 15*(1-s)*t = 12*(1-2*δ) := by
    dsimp only [t]
    field_simp [den.ne', (sub_pos.mpr s1).ne'] <;> ring
  refine ⟨s, ⟨s0.le, s1.le⟩, t, ⟨t0, t1⟩, ?_⟩
  by_cases h : d ≤ 1/2
  · left
    intro i
    apply centered_root_of_params p1 p2
    simpa only [δ, if_pos h] using roots i
  · right
    intro i
    apply centered_root_of_params p1 p2
    change (unitPencil δ κ).eval (1-β i) = 0
    rw [show δ = 1-d from if_neg h, reflect_unitPencil]
    exact roots i

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
