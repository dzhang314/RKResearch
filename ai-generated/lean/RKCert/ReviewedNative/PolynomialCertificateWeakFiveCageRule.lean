module

public import RKCert.ReviewedNative.PolynomialCertificateIntegerDescartes
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCuts

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # A finite row verifier for the 123 conditional weak-five root cages

The ordered tuple consists only of the eight actual sites. The independent
unit-range hypothesis handles the physical endpoints 0 and 1, where the
finite table intentionally does not require a strict half-line count. -/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial
open scoped Polynomial

def centeredIntColumns : IntegerColumns where
  base := [-15, 0, -15, 0, 3135, 0, -10725, 0, 8580]
  inS := [75, 0, -2025, 0, 7425, 0, -6435]
  inT := [0, -525, 0, 5775, 0, -15015, 0, 10725]
  inST := [0, 525, 0, -5775, 0, 15015, 0, -10725]

theorem centeredIntColumns_toRat : centeredIntColumns.toRat = centeredColumns := by
  norm_num [centeredIntColumns, IntegerColumns.toRat, centeredColumns]

theorem centeredIntColumns_width : centeredIntColumns.Within 9 := by decide

def testDen : ℤ := 32768
def centerNum (m : ℕ) : ℤ := 2 * (m : ℤ) - testDen
def centeredThreshold (m : ℕ) : ℚ := (centerNum m : ℚ) / (testDen : ℚ)

theorem testDen_pos : 0 < testDen := by decide

structure CageRow where
  rect : DyadicRect
  ends : List (ℕ × ℕ)
  deriving Repr

def CageRow.endpoint (r : CageRow) (i : ℕ) : ℕ × ℕ :=
  r.ends[i]?.getD (0, 32768)

abbrev CageRow.EndpointOK (r : CageRow) (i : ℕ) : Prop :=
  let m := r.endpoint i
  m.1 ≤ m.2 ∧ m.2 ≤ 32768 ∧
  (m.1 = 0 ∨ integerBudget centeredIntColumns 9 8 (centerNum m.1) testDen r.rect true ≤ i) ∧
  (m.2 = 32768 ∨ integerBudget centeredIntColumns 9 8 (centerNum m.2) testDen r.rect false ≤ 8 - (i + 1))

def CageRow.ok (r : CageRow) : Bool :=
  decide (r.ends.length = 8) && (List.range 8).all (fun i => decide (r.EndpointOK i))

theorem CageRow.endpoint_ok {r : CageRow} (ok : r.ok = true) (i : Fin 8) : r.EndpointOK i.val := by
  exact of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 i.val
    (List.mem_range.mpr i.isLt))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem centeredThreshold_eq (m : ℕ) : (centeredThreshold m : K) = 2 * ((m : K) / 32768) - 1 := by
  simp [centeredThreshold, centerNum, testDen]
  <;> field_simp
  <;> ring

theorem CageRow.centered_sites {r : CageRow} (ok : r.ok = true) {s t : K}
    (cell : InDyadicRect r.rect s t) {β : Fin 8 → K} (order : StrictMono β)
    (unit : ∀ i, β i ∈ Set.Icc (-1) 1)
    (roots : ∀ i, (centeredPolynomial s t).IsRoot (β i)) (i : Fin 8) :
    β i ∈ Set.Icc (centeredThreshold (r.endpoint i.val).1 : K)
      (centeredThreshold (r.endpoint i.val).2 : K) := by
  let p := integerScaledChart centeredIntColumns 9 testDen r.rect s t
  have hscale : (rowScale 9 testDen r.rect : K) ≠ 0 :=
    (Rat.cast_pos.mpr (rowScale_pos 9 testDen_pos r.rect) : (0 : K) < _).ne'
  have hdeg : p.natDegree = 8 := by
    simp only [p, integerScaledChart, natDegree_C_mul hscale, centeredIntColumns_toRat,
      centeredChart_natDegree]
  have hp : p ≠ 0 := by
    intro e
    simp [e] at hdeg
  have hr (j : Fin 8) : p.IsRoot (β j) := by
    change (C (rowScale 9 testDen r.rect : K) *
      rationalChart centeredIntColumns.toRat s t).eval (β j) = 0
    rw [centeredIntColumns_toRat, chart_eq_centeredPolynomial, eval_mul,
      show (centeredPolynomial s t).eval (β j) = 0 from roots j, mul_zero]
  have he := CageRow.endpoint_ok ok i
  constructor
  · rcases he.2.2.1 with edge | bound
    · rw [edge, centeredThreshold_eq]
      simpa using (unit i).1
    · apply le_site_of_below_variations hp order hr i
      exact (below_scaled_variations_le centeredIntColumns 9 8 centeredIntColumns_width
        (centerNum (r.endpoint i.val).1) testDen testDen_pos r.rect cell hdeg.le).trans bound
  · rcases he.2.2.2 with edge | bound
    · rw [edge, centeredThreshold_eq]
      norm_num
      <;> exact (unit i).2
    · apply site_le_of_above_variations hp order hr i
      exact (above_scaled_variations_le centeredIntColumns 9 8 centeredIntColumns_width
        (centerNum (r.endpoint i.val).2) testDen testDen_pos r.rect cell hdeg.le).trans bound

/-- Original unit-interval sites. All bounds are closed and may overlap. -/
theorem CageRow.unit_sites {r : CageRow} (ok : r.ok = true) {s t : K}
    (cell : InDyadicRect r.rect s t) {β : Fin 8 → K} (order : StrictMono β)
    (unit : ∀ i, β i ∈ Set.Icc 0 1)
    (roots : ∀ i, (centeredPolynomial s t).IsRoot (2 * β i - 1)) (i : Fin 8) :
    β i ∈ Set.Icc (((r.endpoint i.val).1 : K) / 32768)
      (((r.endpoint i.val).2 : K) / 32768) := by
  let γ := fun j : Fin 8 => 2 * β j - 1
  have inc : StrictMono γ := by
    intro j k hjk
    dsimp [γ]
    linarith only [order hjk]
  have un (j : Fin 8) : γ j ∈ Set.Icc (-1) 1 := by
    constructor <;> dsimp [γ] <;> linarith only [(unit j).1, (unit j).2]
  have h := CageRow.centered_sites ok cell inc un roots i
  have lower := h.1
  have upper := h.2
  rw [centeredThreshold_eq] at lower upper
  dsimp [γ] at lower upper
  constructor <;> linarith only [lower, upper]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
