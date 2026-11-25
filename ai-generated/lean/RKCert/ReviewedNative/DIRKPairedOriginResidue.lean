module

public import RKCert.ReviewedNative.GradedColumns
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Order.Interval.Finset.Fin

import Mathlib.Tactic.Ring

@[expose] public section

/-! # Paired origin-zero receipts on the unchanged diagonal tableau

These statements use true derivative stage defects, not the defect of a
diagonal-stripped tableau. The local receiver argument requires only its
upper-triangular entries to vanish, its own diagonal, and the actual earlier
joint-clean clock condition. No order, payment, or stage bound is claimed. -/
namespace RKResearch.Certified.Graded.PairedOrigin

open Polynomial
open scoped Classical Matrix

variable {K : Type*} [Field K]

/-- The primitive whose derivative annihilates the origin clock. -/
noncomputable def originPrimitive (γ : K) : K[X] := X * (X - C γ)^2

/-- The adjacent primitive clears the nonorigin resonances of its partner. -/
noncomputable def nextPrimitive (γ : K) : K[X] := X * originPrimitive γ

/-- The scalar clock receipt remaining after the diagonal pays itself. -/
noncomputable def receiptPoly (γ : K) (P : K[X]) : K[X] :=
  P - C γ * P.derivative

theorem eval_originPrimitive (γ x : K) :
    (originPrimitive γ).eval x = x * (x - γ)^2 := by
  simp only [originPrimitive, eval_mul, eval_X, eval_pow, eval_sub, eval_C]

theorem eval_derivative_originPrimitive (γ x : K) :
    (originPrimitive γ).derivative.eval x = (x - γ)^2 + x * (2 * (x - γ)) := by
  simp only [originPrimitive, derivative_mul, derivative_X, one_mul,
    derivative_X_sub_C_sq, eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C]

theorem eval_nextPrimitive (γ x : K) :
    (nextPrimitive γ).eval x = x * (originPrimitive γ).eval x := by
  simp only [nextPrimitive, eval_mul, eval_X]

theorem eval_derivative_nextPrimitive (γ x : K) :
    (nextPrimitive γ).derivative.eval x =
      (originPrimitive γ).eval x + x * (originPrimitive γ).derivative.eval x := by
  simp only [nextPrimitive, derivative_mul, derivative_X, one_mul, eval_add, eval_mul, eval_X]

theorem eval_receiptPoly (γ x : K) (P : K[X]) :
    (receiptPoly γ P).eval x = P.eval x - γ * P.derivative.eval x := by
  simp only [receiptPoly, eval_sub, eval_mul, eval_C]

/-- The derivative product rule gives the exact triangular relation
between the two receipt polynomials, without any divisions. -/
theorem receiptPoly_X_mul (γ : K) (P : K[X]) :
    receiptPoly γ (X * P) = X * receiptPoly γ P - C γ * P := by
  simp only [receiptPoly, derivative_mul, derivative_X, one_mul]
  ring

theorem primitive_double_zero (γ : K) :
    ((originPrimitive γ).eval γ = 0 ∧ (originPrimitive γ).derivative.eval γ = 0) ∧
      ((nextPrimitive γ).eval γ = 0 ∧ (nextPrimitive γ).derivative.eval γ = 0) := by
  simp [eval_nextPrimitive, eval_derivative_nextPrimitive,
    eval_originPrimitive, eval_derivative_originPrimitive]

/-- Both receipts vanish exactly at the origin clock. Apart from its
being nonzero, the diagonal needs no small characteristic units. -/
theorem pair_receipt_zero_iff (γ x : K) (hγ : γ ≠ 0) :
    (receiptPoly γ (originPrimitive γ)).eval x = 0 ∧
      (receiptPoly γ (nextPrimitive γ)).eval x = 0 ↔ x = γ := by
  constructor
  · rintro ⟨first, second⟩
    have val : (originPrimitive γ).eval x = 0 := by
      rw [nextPrimitive, receiptPoly_X_mul, eval_sub, eval_mul, eval_X,
        eval_mul, eval_C, first, mul_zero, zero_sub, neg_eq_zero] at second
      exact (mul_eq_zero.mp second).resolve_left hγ
    have der : (originPrimitive γ).derivative.eval x = 0 := by
      rw [eval_receiptPoly, val, zero_sub, neg_eq_zero] at first
      exact (mul_eq_zero.mp first).resolve_left hγ
    by_contra ne
    have x0 : x = 0 := by
      rw [eval_originPrimitive] at val
      exact (mul_eq_zero.mp val).resolve_right (pow_ne_zero 2 (sub_ne_zero.mpr ne))
    rw [x0, eval_derivative_originPrimitive, zero_sub, zero_mul, add_zero] at der
    exact (pow_ne_zero 2 (neg_ne_zero.mpr hγ)) der
  · intro same; rw [same]
    obtain ⟨⟨v, dv⟩, ⟨w, dw⟩⟩ := primitive_double_zero γ
    exact ⟨by rw [eval_receiptPoly, v, dv, mul_zero, sub_zero],
      by rw [eval_receiptPoly, w, dw, mul_zero, sub_zero]⟩

noncomputable def stageResidual {s : ℕ} (A : Matrix (Fin s) (Fin s) K)
    (P : K[X]) (k : Fin s) : K :=
  mat A (fun i => P.derivative.eval (nodes A i)) k - P.eval (nodes A k)

noncomputable def pastReceipt {s : ℕ} (A : Matrix (Fin s) (Fin s) K)
    (P : K[X]) (k : Fin s) : K :=
  ∑ i ∈ Finset.Iio k, A k i * P.derivative.eval (nodes A i)

variable {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {k : Fin s} {γ : K}

private theorem mat_add_diagonal_of_row
    (upper : ∀ i, k < i → A k i = 0) (v : Fin s → K) :
    mat A v k = (∑ i ∈ Finset.Iio k, A k i * v i) + A k k * v k := by
  classical
  have no : k ∉ Finset.Iio k := fun h => (lt_irrefl k) (Finset.mem_Iio.mp h)
  rw [mat_apply, Matrix.mulVec, dotProduct]
  have cut : (∑ i ∈ insert k (Finset.Iio k), A k i * v i) =
      ∑ i : Fin s, A k i * v i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ ni
    have nlt : ¬ i < k := fun p => ni (Finset.mem_insert.mpr (Or.inr (Finset.mem_Iio.mpr p)))
    have nke : k ≠ i := fun e => ni (Finset.mem_insert.mpr (Or.inl e.symm))
    rw [upper i (lt_of_le_of_ne (le_of_not_gt nlt) nke), zero_mul]
  rw [←cut, Finset.sum_insert no, add_comm]

/-- At a clean recipient the diagonal only subtracts the term
from its own derivative evaluation. -/
theorem pastReceipt_eq_eval_of_clean
    (upper : ∀ i, k < i → A k i = 0) (diagonal : A k k = γ)
    (P : K[X]) (clean : stageResidual A P k = 0) :
    pastReceipt A P k = (receiptPoly γ P).eval (nodes A k) := by
  have m : mat A (fun i => P.derivative.eval (nodes A i)) k = P.eval (nodes A k) :=
    sub_eq_zero.mp (show mat A (fun i => P.derivative.eval (nodes A i)) k -
      P.eval (nodes A k) = 0 from clean)
  rw [mat_add_diagonal_of_row upper, diagonal] at m
  rw [pastReceipt, eval_receiptPoly]
  exact (eq_sub_iff_add_eq).mpr m

/-- The actual origin is jointly clean over any field. Only its own
diagonal and upper entries are used; common diagonals elsewhere are irrelevant. -/
theorem paired_actual_origin_clean {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (upper : ∀ i, (0 : Fin (n+1)) < i → B 0 i = 0) (diagonal : B 0 0 = γ) :
    stageResidual B (originPrimitive γ) 0 = 0 ∧ stageResidual B (nextPrimitive γ) 0 = 0 := by
  have sing (v : Fin (n+1) → K) : mat B v 0 = γ * v 0 := by
    rw [mat_apply, Matrix.mulVec, dotProduct, Finset.sum_eq_single 0]
    · rw [diagonal]
    · intro i _ nz
      rw [upper i (lt_of_le_of_ne (Fin.zero_le i) (fun e => nz e.symm)), zero_mul]
    · intro no
      exact (no (Finset.mem_univ _)).elim
  have node : nodes B 0 = γ := by
    change mat B (1 : Fin (n+1) → K) 0 = γ
    simpa only [Pi.one_apply, mul_one] using sing (1 : Fin (n+1) → K)
  obtain ⟨⟨v, dv⟩, ⟨w, dw⟩⟩ := primitive_double_zero γ
  constructor
  · rw [stageResidual, sing, node, v, dv, mul_zero, sub_self]
  · rw [stageResidual, sing, node, w, dw, mul_zero, sub_self]

/-- The first nonorigin joint-clean clock cannot have both prior
receipts zero. This formulation does not yet discard earlier clean copies. -/
theorem paired_pastReceipt_ne_of_clean
    (hγ : γ ≠ 0) (upper : ∀ i, k < i → A k i = 0) (diagonal : A k k = γ)
    (cleanG : stageResidual A (originPrimitive γ) k = 0)
    (cleanH : stageResidual A (nextPrimitive γ) k = 0)
    (nonorigin : nodes A k ≠ γ) :
    pastReceipt A (originPrimitive γ) k ≠ 0 ∨ pastReceipt A (nextPrimitive γ) k ≠ 0 := by
  by_cases h : pastReceipt A (originPrimitive γ) k = 0
  · right
    intro t
    have first := (pastReceipt_eq_eval_of_clean upper diagonal _ cleanG).symm.trans h
    have second := (pastReceipt_eq_eval_of_clean upper diagonal _ cleanH).symm.trans t
    exact nonorigin ((pair_receipt_zero_iff γ (nodes A k) hγ).mp ⟨first, second⟩)
  · exact Or.inl h

/-- Joint-off strictly earlier physical stages, not a clock quotient. -/
noncomputable def earlierJointOffRows (A : Matrix (Fin s) (Fin s) K)
    (γ : K) (k : Fin s) : Finset (Fin s) :=
  (Finset.Iio k).filter (fun i => ¬ (stageResidual A (originPrimitive γ) i = 0 ∧
    stageResidual A (nextPrimitive γ) i = 0))

/-- If all earlier joint-clean clocks are the origin clock, the same
nonzero receipt comes entirely from the true earlier joint-off rows. -/
theorem paired_offReceipt_ne_of_first_nonorigin
    (hγ : γ ≠ 0) (upper : ∀ i, k < i → A k i = 0) (diagonal : A k k = γ)
    (cleanG : stageResidual A (originPrimitive γ) k = 0)
    (cleanH : stageResidual A (nextPrimitive γ) k = 0)
    (nonorigin : nodes A k ≠ γ)
    (earlier : ∀ i, i < k → stageResidual A (originPrimitive γ) i = 0 →
      stageResidual A (nextPrimitive γ) i = 0 → nodes A i = γ) :
    (∑ i ∈ earlierJointOffRows A γ k, A k i * (originPrimitive γ).derivative.eval (nodes A i)) ≠ 0 ∨
      (∑ i ∈ earlierJointOffRows A γ k, A k i * (nextPrimitive γ).derivative.eval (nodes A i)) ≠ 0 := by
  classical
  have drop (P : K[X]) (z : P.derivative.eval γ = 0) :
      (∑ i ∈ earlierJointOffRows A γ k, A k i * P.derivative.eval (nodes A i)) =
        pastReceipt A P k := by
    rw [pastReceipt]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi no
    have ic : stageResidual A (originPrimitive γ) i = 0 ∧
        stageResidual A (nextPrimitive γ) i = 0 := by
      by_contra n
      exact no (Finset.mem_filter.mpr ⟨hi, n⟩)
    rw [earlier i (Finset.mem_Iio.mp hi) ic.1 ic.2, z, mul_zero]
  have zeros := primitive_double_zero γ
  rw [drop (originPrimitive γ) zeros.1.2, drop (nextPrimitive γ) zeros.2.2]
  exact paired_pastReceipt_ne_of_clean hγ upper diagonal cleanG cleanH nonorigin

end RKResearch.Certified.Graded.PairedOrigin
