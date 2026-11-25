module

public import RKCert.ReviewedNative.FiniteOrderedSignWindows
public import Mathlib.Algebra.Polynomial.OfFn

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Two universal Jacobi polynomials and a degree-seven obstruction -/

namespace RKCert.ReviewedNative.JacobiSix

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns
open scoped BigOperators Classical

noncomputable section

def a6 (K : Type*) [Field K] : Fin 7 → K :=
  ![1/429, -27/429, 225/429, -825/429, 1485/429, -1287/429, 1]

def a7 (K : Type*) [Field K] : Fin 8 → K :=
  ![-1/1430, 35/1430, -385/1430, 1925/1430, -5005/1430, 7007/1430, -5005/1430, 1]

/-- Monic degree six for the weight X(1-X) on the unit interval. -/
def J6 (K : Type*) [Field K] : K[X] := ofFn 7 (a6 K)

/-- Monic degree seven for the weight X(1-X) on the unit interval. -/
def J7 (K : Type*) [Field K] : K[X] := ofFn 8 (a7 K)

theorem J6_coeff_top (K : Type*) [Field K] : (J6 K).coeff 6 = 1 := by
  rw [J6, ofFn_coeff_eq_val_of_lt _ (show 6 < 7 by decide)] <;> norm_num [a6]

theorem J7_coeff_top (K : Type*) [Field K] : (J7 K).coeff 7 = 1 := by
  rw [J7, ofFn_coeff_eq_val_of_lt _ (show 7 < 8 by decide)] <;> norm_num [a7]

theorem J6_natDegree (K : Type*) [Field K] : (J6 K).natDegree = 6 := by
  have d : (J6 K).natDegree < 7 := ofFn_natDegree_lt (by decide) (a6 K)
  apply natDegree_eq_of_le_of_coeff_ne_zero (by omega)
  simpa only [J6_coeff_top] using (one_ne_zero : (1 : K) ≠ 0)

theorem J7_natDegree (K : Type*) [Field K] : (J7 K).natDegree = 7 := by
  have d : (J7 K).natDegree < 8 := ofFn_natDegree_lt (by decide) (a7 K)
  apply natDegree_eq_of_le_of_coeff_ne_zero (by omega)
  simpa only [J7_coeff_top] using (one_ne_zero : (1 : K) ≠ 0)

theorem J6_monic (K : Type*) [Field K] : (J6 K).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one 6 (J6_natDegree K).le (J6_coeff_top K)

theorem J7_monic (K : Type*) [Field K] : (J7 K).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one 7 (J7_natDegree K).le (J7_coeff_top K)

section Formal
variable {K : Type*} [Field K] [CharZero K]

/-- Exact audited centered formula, evaluated at any field point. -/
theorem J6_eval_centered (x : K) :
    (J6 K).eval x =
      (429*(2*x-1)^6 - 495*(2*x-1)^4 + 135*(2*x-1)^2 - 5)/(429*2^6) := by
  rw [J6, ofFn_eq_sum_monomial, eval_finsetSum]
  simp only [eval_monomial]
  norm_num [Fin.sum_univ_succ, a6] <;> ring

/-- Exact audited centered formula, evaluated at any field point. -/
theorem J7_eval_centered (x : K) :
    (J7 K).eval x =
      (715*(2*x-1)^7 - 1001*(2*x-1)^5 + 385*(2*x-1)^3 - 35*(2*x-1))/
        (715*2^7) := by
  rw [J7, ofFn_eq_sum_monomial, eval_finsetSum]
  simp only [eval_monomial]
  norm_num [Fin.sum_univ_succ, a7] <;> ring

/-- Orthogonality to the entire polynomial space through degree five. -/
def OrthogonalSix (Q : K[X]) : Prop :=
  ∀ R : K[X], R.natDegree ≤ 5 → integral 0 1 (X * (1 - X) * Q * R) = 0

private theorem integral_monomial_unit (i : ℕ) (a : K) :
    integral 0 1 (monomial i a) = a / ((i+1 : ℕ) : K) := by
  by_cases h : a = 0
  · simp [h, formalPrimitive]
  rw [integral_zero_left]
  simp [formalPrimitive, support_monomial i h]

/-- The two rational terms contributed by one coefficient in a paid test. -/
private theorem weighted_monomial (i k : ℕ) (a : K) :
    integral 0 1 (X * (1-X) * monomial i a * X^k) =
      a / ((i+k+2 : ℕ) : K) - a / ((i+k+3 : ℕ) : K) := by
  have expand : (X : K[X]) * (1-X) * monomial i a * X^k =
      monomial (i+k+1) a - monomial (i+k+2) a := by
    simp only [← C_mul_X_pow_eq_monomial, pow_add, pow_one, pow_two]
    ring
  rw [expand, map_sub, integral_monomial_unit, integral_monomial_unit]

private theorem weighted_vector_moment {n : ℕ} (a : Fin n → K) (k : ℕ) :
    integral 0 1 (X * (1-X) * ofFn n a * X^k) =
      ∑ i : Fin n, (a i / ((i.val+k+2 : ℕ) : K) -
        a i / ((i.val+k+3 : ℕ) : K)) := by
  rw [ofFn_eq_sum_monomial, Finset.mul_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact weighted_monomial i.val k (a i)

private theorem J6_power_paid (k : Fin 6) :
    integral 0 1 (X * (1-X) * J6 K * X^k.val) = 0 := by
  rw [J6, weighted_vector_moment]
  fin_cases k <;> norm_num [Fin.sum_univ_succ, a6]

private theorem J7_power_paid (k : Fin 6) :
    integral 0 1 (X * (1-X) * J7 K * X^k.val) = 0 := by
  rw [J7, weighted_vector_moment]
  fin_cases k <;> norm_num [Fin.sum_univ_succ, a7]

private theorem orthogonal_of_powers {Q : K[X]}
    (h : ∀ k : Fin 6, integral 0 1 (X * (1-X) * Q * X^k.val) = 0) :
    OrthogonalSix Q := by
  intro R hr
  let L : K[X] →ₗ[K] K :=
    (integral 0 1).comp (LinearMap.mulLeft K (X * (1-X) * Q))
  change L R = 0
  rw [R.as_sum_range' 6 (by omega), map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have z : L (X^i) = 0 := h ⟨i, Finset.mem_range.mp hi⟩
  rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, z, smul_zero]

theorem J6_orthogonal : OrthogonalSix (J6 K) := orthogonal_of_powers J6_power_paid

theorem J7_orthogonal : OrthogonalSix (J7 K) := orthogonal_of_powers J7_power_paid

end Formal

section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem zero_of_small_orthogonal {D : K[X]} (small : D.natDegree ≤ 5)
    (h : OrthogonalSix D) : D = 0 := by
  by_contra hn
  have lr : (0 : K) < 1 := zero_lt_one
  have oneX : (1 - X : K[X]).natDegree ≤ 1 := by
    simpa only [natDegree_one, natDegree_X, max_eq_right (Nat.zero_le 1)] using
      (natDegree_sub_le (1 : K[X]) (X : K[X]))
  have wdeg : ((X : K[X]) * (1-X)).natDegree ≤ 2 :=
    natDegree_mul_le_of_le (by simp : (X : K[X]).natDegree ≤ 1) oneX
  have wd : (X * (1-X) * D).natDegree ≤ 7 := natDegree_mul_le_of_le wdeg small
  have wd2 : (X * (1-X) * D * D).natDegree ≤ 12 := natDegree_mul_le_of_le wd small
  have v (i : Fin 19) :
      (X * (1-X) * D * D).eval (intervalPoint 0 1 i) =
      let x := intervalPoint (0 : K) 1 i
      (x * (1-x)) * (D.eval x * D.eval x) := by
    simp only [eval_mul, eval_sub, eval_one, eval_X, mul_assoc]
  have massPos (i : Fin 19) : 0 < intervalPoint (0 : K) 1 i *
      (1 - intervalPoint (0 : K) 1 i) := by
    have hi := intervalPoint_mem lr i
    exact mul_pos hi.1 (sub_pos.mpr hi.2)
  have nonneg (i : Fin 19) : 0 ≤ (X * (1-X) * D * D).eval (intervalPoint 0 1 i) := by
    rw [v i]
    exact mul_nonneg (massPos i).le (mul_self_nonneg _)
  obtain ⟨i, hi⟩ := exists_nonzero_grid_sample lr hn (by omega : D.natDegree < 19)
  have pos : 0 < (X * (1-X) * D * D).eval (intervalPoint 0 1 i) := by
    rw [v i]
    exact mul_pos (massPos i) (mul_self_pos.mpr hi)
  have ig : 0 < integral 0 1 (X * (1-X) * D * D) :=
    integral_pos_of_grid_samples lr (wd2.trans (by decide)) nonneg ⟨i, pos⟩
  exact (ne_of_gt ig) (h D small)

/-- The full degree-seven pencil, with the coefficient earned by exact
orthogonality and positivity rather than a prespecified numerical value. -/
theorem monic_seven_pencil {Q : K[X]} (mq : Q.Monic) (qd : Q.natDegree = 7)
    (h : OrthogonalSix Q) : ∃ a : K, Q = J7 K + C a * J6 K := by
  let a := Q.coeff 6 - (J7 K).coeff 6
  let D := Q - J7 K - C a * J6 K
  have q7 : Q.coeff 7 = 1 := by
    rw [← qd, coeff_natDegree]
    exact mq.leadingCoeff
  have j67 : (J6 K).coeff 7 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [J6_natDegree]; decide)
  have dD : D.natDegree ≤ 5 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rcases (show i = 6 ∨ i = 7 ∨ 7 < i by omega) with e | e | big
    · subst i
      simp only [D, coeff_sub, coeff_C_mul, J6_coeff_top, mul_one, a, sub_self]
    · subst i
      simp only [D, coeff_sub, coeff_C_mul, q7, J7_coeff_top, j67, mul_zero, sub_self, sub_zero]
    · have zq : Q.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      have z6 : (J6 K).coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by rw [J6_natDegree]; omega)
      have z7 : (J7 K).coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by rw [J7_natDegree]; omega)
      simp only [D, coeff_sub, coeff_C_mul, zq, z6, z7, mul_zero, sub_zero]
  have od : OrthogonalSix D := by
    intro R rd
    have expand : X * (1-X) * D * R =
        (X * (1-X) * Q * R) - (X * (1-X) * J7 K * R) -
          a • (X * (1-X) * J6 K * R) := by
      dsimp only [D]
      rw [smul_eq_C_mul]
      ring
    rw [expand]
    simp only [map_sub, map_smul, h R rd, J7_orthogonal R rd, J6_orthogonal R rd,
      smul_zero, sub_zero]
  have D0 := zero_of_small_orthogonal dD od
  change Q - J7 K - C a * J6 K = 0 at D0
  refine ⟨a, ?_⟩
  calc
    Q = (Q - J7 K - C a * J6 K) + (J7 K + C a * J6 K) := by ring
    _ = J7 K + C a * J6 K := by rw [D0, zero_add]

theorem signs_at_fourteen_fifteenths :
    (J6 K).eval (14/15) < 0 ∧ (J7 K).eval (14/15) < 0 := by
  constructor
  · rw [J6_eval_centered]
    norm_num
  · rw [J7_eval_centered]
    norm_num

theorem signs_at_fifteen_sixteenths :
    0 < (J6 K).eval (15/16) ∧ (J7 K).eval (15/16) < 0 := by
  constructor
  · rw [J6_eval_centered]
    norm_num
  · rw [J7_eval_centered]
    norm_num

/-- Every coefficient of the neutral pencil fails at
one of the two exact rational sample points. -/
theorem not_monic_seven_positive_at_cut_points {Q : K[X]}
    (mq : Q.Monic) (qd : Q.natDegree = 7) (h : OrthogonalSix Q)
    (left : 0 < Q.eval (14/15)) (right : 0 < Q.eval (15/16)) : False := by
  obtain ⟨a, eq⟩ := monic_seven_pencil mq qd h
  rcases le_or_gt 0 a with ap | an
  · obtain ⟨j6, j7⟩ := signs_at_fourteen_fifteenths (K := K)
    have product : a * (J6 K).eval (14/15) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ap j6.le
    have bad : Q.eval (14/15) < 0 := by
      rw [eq, eval_add, eval_mul, eval_C]
      exact (add_le_add (le_refl _) product).trans_lt (by simpa only [add_zero] using j7)
    exact (not_lt_of_ge left.le) bad
  · obtain ⟨j6, j7⟩ := signs_at_fifteen_sixteenths (K := K)
    have product : a * (J6 K).eval (15/16) ≤ 0 := (mul_neg_of_neg_of_pos an j6).le
    have bad : Q.eval (15/16) < 0 := by
      rw [eq, eval_add, eval_mul, eval_C]
      exact (add_le_add (le_refl _) product).trans_lt (by simpa only [add_zero] using j7)
    exact (not_lt_of_ge right.le) bad

end Ordered
end
end RKCert.ReviewedNative.JacobiSix
