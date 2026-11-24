module

public import RKCert.ReviewedNative.DisplayedFactorDegreeBudget

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Paid tests on already guarded and grouped unit moments -/

namespace RKCert.ReviewedNative.FiniteOrderedSigns

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19
open scoped BigOperators

noncomputable section

section Algebraic

variable {K : Type*} [Field K] [CharZero K]

/-- The weight U and the clock aggregates have already absorbed the guard.
The bound b is the remaining polynomial test degree after this payment.
No underlying row type or chosen representatives enter the law. -/
def GroupedUnitMoments
    (U q : K[X]) (T : Finset K) (μ : K → K) (b : ℕ) : Prop :=
  ∀ H : K[X], H.natDegree ≤ b →
    integral 0 1 (U * q * H) = ∑ r ∈ T, μ r * H.eval r

/-- A nodal multiplier kills the grouped measure at exactly the paid cost. -/
theorem GroupedUnitMoments.nodal_orthogonality
    {U q : K[X]} {T : Finset K} {μ : K → K} {b d : ℕ}
    (law : GroupedUnitMoments U q T μ b) (room : T.card + d ≤ b)
    (H : K[X]) (hd : H.natDegree ≤ d) :
    integral 0 1 (U * (q * nodalHull T) * H) = 0 := by
  have degree : (nodalHull T * H).natDegree ≤ b :=
    (natDegree_mul_le_of_le (natDegree_nodalHull T).le hd).trans room
  have zero : (∑ r ∈ T, μ r * (nodalHull T * H).eval r) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    simp only [eval_mul, nodalHull_eval_of_mem hr, zero_mul, mul_zero]
  have paid := (law (nodalHull T * H) degree).trans zero
  simpa only [mul_assoc] using paid

end Algebraic

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The exact guarded deficit, stated without truncated natural subtraction
in the conclusion. When there are too many sites to spend the nodal hull,
the bound follows already from the degree of the displayed factor. -/
theorem GroupedUnitMoments.displayed_factor_budget
    {U q F G : K[X]} {T : Finset K} {μ : K → K} {b : ℕ}
    (law : GroupedUnitMoments U q T μ b) (qn : q ≠ 0)
    (factor : q * nodalHull T = F * G)
    (weightPos : ∀ i : Fin 19, 0 < U.eval (intervalPoint (0 : K) 1 i))
    (fixedSign :
      (∀ i : Fin 19, 0 ≤ F.eval (intervalPoint (0 : K) 1 i)) ∨
      (∀ i : Fin 19, F.eval (intervalPoint (0 : K) 1 i) ≤ 0))
    (grid : U.natDegree + q.natDegree + b < 19) :
    b + 1 + F.natDegree ≤ q.natDegree + 2 * T.card := by
  have nn : nodalHull T ≠ 0 := (monic_nodalHull T).ne_zero
  have mn : q * nodalHull T ≠ 0 := mul_ne_zero qn nn
  have degreeM : (q * nodalHull T).natDegree = q.natDegree + T.card := by
    rw [natDegree_mul qn nn, natDegree_nodalHull]
  by_cases ht : T.card ≤ b
  · let d : ℕ := b - T.card
    have paid : T.card + d = b := Nat.add_sub_of_le ht
    have budget : U.natDegree + (q * nodalHull T).natDegree + d < 19 := by
      rw [degreeM]
      simpa only [Nat.add_assoc, paid] using grid
    have charge := displayed_factor_degree_budget mn factor weightPos fixedSign budget
      (law.nodal_orthogonality paid.le)
    rw [degreeM] at charge
    omega
  · have fn : F ≠ 0 := fun h => mn (by rw [factor, h, zero_mul])
    have gn : G ≠ 0 := fun h => mn (by rw [factor, h, mul_zero])
    have split : q.natDegree + T.card = F.natDegree + G.natDegree := by
      rw [← degreeM, factor, natDegree_mul fn gn]
    omega

/-- Square the nodal hull of the complement to isolate the selected clocks.
Only positivity of the product U * L on the fixed grid is required. -/
theorem GroupedUnitMoments.subset_localizer_pos
    {U q L : K[X]} {T J : Finset K} {μ : K → K} {b : ℕ}
    (law : GroupedUnitMoments U q T μ b) (sub : J ⊆ T) (qn : q ≠ 0)
    (room : L.natDegree + q.natDegree + 2 * (T.card - J.card) ≤ b)
    (grid : U.natDegree + q.natDegree + b < 19)
    (weightPos : ∀ i : Fin 19, 0 < (U * L).eval (intervalPoint (0 : K) 1 i)) :
    0 < ∑ r ∈ J, μ r * (L.eval r * q.eval r * ((nodalHull (T \ J)).eval r)^2) := by
  let S : K[X] := nodalHull (T \ J)
  let H : K[X] := L * q * S^2
  have sd : S.natDegree = T.card - J.card := by
    dsimp only [S]
    rw [natDegree_nodalHull, Finset.card_sdiff_of_subset sub]
  have hd : H.natDegree ≤ b := by
    dsimp only [H]
    exact (natDegree_mul_le_of_le (natDegree_mul_le (p := L) (q := q))
      (natDegree_pow_le_of_le 2 sd.le)).trans room
  have sn : S ≠ 0 := (monic_nodalHull (T \ J)).ne_zero
  have wne : U * L ≠ 0 := by
    intro e
    have live := weightPos (0 : Fin 19)
    rw [e, eval_zero] at live
    exact (lt_irrefl (0 : K)) live
  let trial : K[X] := U * q * H
  have shape : trial = (U * L) * (q * S)^2 := by
    simp only [trial, H, pow_two]
    ac_rfl
  have tn : trial ≠ 0 := by
    rw [shape]
    exact mul_ne_zero wne (pow_ne_zero 2 (mul_ne_zero qn sn))
  have td : trial.natDegree < 19 := by
    dsimp only [trial]
    exact (natDegree_mul_le_of_le (natDegree_mul_le (p := U) (q := q)) hd).trans_lt grid
  have nonneg (i : Fin 19) : 0 ≤ trial.eval (intervalPoint (0 : K) 1 i) := by
    rw [shape, eval_mul (p := U * L) (q := (q * S)^2), eval_pow]
    exact mul_nonneg (weightPos i).le (sq_nonneg _)
  have unit : (0 : K) < 1 := zero_lt_one
  obtain ⟨i, live⟩ := exists_nonzero_grid_sample unit tn td
  have pos : 0 < integral 0 1 trial :=
    integral_pos_of_grid_samples unit td.le nonneg
      ⟨i, lt_of_le_of_ne (nonneg i) live.symm⟩
  have moment : integral 0 1 trial = ∑ r ∈ T, μ r * H.eval r := law H hd
  have restrictSum :
      (∑ r ∈ J, μ r * H.eval r) = ∑ r ∈ T, μ r * H.eval r := by
    apply Finset.sum_subset sub
    intro r hr nr
    have z : S.eval r = 0 := nodalHull_eval_of_mem (Finset.mem_sdiff.mpr ⟨hr, nr⟩)
    simp only [H, eval_mul, eval_pow, z, pow_two, zero_mul, mul_zero]
  rw [moment, ← restrictSum] at pos
  simpa only [H, S, eval_mul, eval_pow] using pos

end Ordered

end

end RKCert.ReviewedNative.FiniteOrderedSigns
