module

public import Mathlib.Algebra.Polynomial.RuleOfSigns
public import Mathlib.Data.Rat.Cast.Order

import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Computable coefficient sign budgets

The exhaustive evaluator is intentionally simple. It keeps the zero choice
when allowed, pads leading zeros up to a common degree, and bounds the
actual Descartes variation count by integer arithmetic. -/

namespace RKCert.ReviewedNative.PolynomialCertificate

open Polynomial SignType
open scoped Polynomial

/-- Enumerate the length-m sign words in descending coefficient order. -/
def signWords (choices : ℕ → List SignType) : ℕ → List (List SignType)
  | 0 => [[]]
  | m + 1 => (choices m).flatMap fun s =>
      (signWords choices m).map (List.cons s)

def variationBudget (choices : ℕ → List SignType) (m : ℕ) : ℕ :=
  (signWords choices m).foldr (fun w b => max w.signVariations b) 0

private theorem mem_signWords_of_mem {choices : ℕ → List SignType} {s : ℕ → SignType}
    (m : ℕ) (h : ∀ j < m, s j ∈ choices j) :
    (List.range m).reverse.map s ∈ signWords choices m := by
  induction m with
  | zero => simp [signWords]
  | succ m ih =>
      rw [List.range_succ, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.map_cons, signWords, List.mem_flatMap]
      exact ⟨s m, h m (Nat.lt_succ_self _),
        List.mem_map.mpr ⟨_, ih (fun j hj => h j (Nat.lt.step hj)), rfl⟩⟩

private theorem variations_le_fold_of_mem {words : List (List SignType)} {w : List SignType}
    (hw : w ∈ words) :
    w.signVariations ≤ words.foldr (fun s b => max s.signVariations b) 0 := by
  induction words with
  | nil => simp at hw
  | cons s words ih =>
      rcases List.mem_cons.mp hw with equality | h
      · subst w
        exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)

theorem variation_le_budget_of_mem {choices : ℕ → List SignType} {m : ℕ}
    {w : List SignType} (hw : w ∈ signWords choices m) :
    w.signVariations ≤ variationBudget choices m :=
  variations_le_fold_of_mem hw

section Ordered

variable {K : Type*} [Semiring K] [LinearOrder K]

/-- Allowed signs from a closed interval. A possibly vanishing coefficient
does not have to be assigned a nonzero sign. -/
def allowedSigns (l u : K) : List SignType :=
  (if l < 0 then [-1] else []) ++
    (if l ≤ 0 ∧ 0 ≤ u then [0] else []) ++
    (if 0 < u then [1] else [])

theorem sign_mem_allowedSigns {l u x : K} (hl : l ≤ x) (hu : x ≤ u) :
    sign x ∈ allowedSigns l u := by
  rcases lt_trichotomy x 0 with h | h | h
  · have hneg : l < 0 := hl.trans_lt h
    rw [sign_eq_neg_one_iff.mpr h]
    simp [allowedSigns, hneg]
  · subst x
    simp [allowedSigns, hl, hu]
  · have hpos : 0 < u := h.trans_le hu
    rw [sign_eq_one_iff.mpr h]
    simp [allowedSigns, hpos]

private theorem padded_signVariations_eq {p : K[X]} (hp : p ≠ 0) (m : ℕ) :
    ((List.range (p.natDegree + 1 + m)).reverse.map p.coeff).signVariations =
      p.signVariations := by
  induction m with
  | zero =>
      simp only [Nat.add_zero, Polynomial.signVariations, Polynomial.coeffList_of_ne_zero hp]
  | succ m ih =>
      simp only [Nat.add_succ, List.range_succ, List.reverse_append,
        List.reverse_singleton, List.singleton_append, List.map_cons]
      have hz : p.coeff (p.natDegree + 1 + m) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hz, List.signVariations_zero_cons, ih]

theorem signVariations_le_variationBudget {p : K[X]} {d : ℕ} (hd : p.natDegree ≤ d)
    {choices : ℕ → List SignType}
    (h : ∀ j ≤ d, sign (p.coeff j) ∈ choices j) :
    p.signVariations ≤ variationBudget choices (d + 1) := by
  by_cases hp : p = 0
  · subst p
    simpa only [Polynomial.signVariations_zero] using
      (Nat.zero_le (variationBudget choices (d + 1)))
  have hpad :
      ((List.range (d + 1)).reverse.map p.coeff).signVariations = p.signVariations := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show p.natDegree + 1 ≤ d + 1 by omega)
    simpa only [← hm] using padded_signVariations_eq hp m
  have hm : (List.range (d + 1)).reverse.map (fun j => sign (p.coeff j)) ∈
      signWords choices (d + 1) :=
    mem_signWords_of_mem (d + 1) (fun j hj => h j (Nat.le_of_lt_succ hj))
  calc
    p.signVariations = ((List.range (d + 1)).reverse.map p.coeff).signVariations := hpad.symm
    _ = (((List.range (d + 1)).reverse.map p.coeff).map sign).signVariations :=
      (List.signVariations_map_sign _).symm
    _ ≤ variationBudget choices (d + 1) := by
      rw [List.map_map]
      exact variation_le_budget_of_mem hm

def coeffVariationBudget (d : ℕ) (l u : ℕ → K) : ℕ :=
  variationBudget (fun j => allowedSigns (l j) (u j)) (d + 1)

theorem signVariations_le_coeffVariationBudget {p : K[X]} {d : ℕ}
    (hd : p.natDegree ≤ d) {l u : ℕ → K}
    (h : ∀ j ≤ d, l j ≤ p.coeff j ∧ p.coeff j ≤ u j) :
    p.signVariations ≤ coeffVariationBudget d l u :=
  signVariations_le_variationBudget hd fun j hj =>
    sign_mem_allowedSigns (h j hj).1 (h j hj).2

end Ordered

section Rational

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

@[simp] theorem allowedSigns_ratCast (l u : ℚ) :
    allowedSigns (l : K) (u : K) = allowedSigns l u := by
  simp [allowedSigns]

@[simp] theorem coeffVariationBudget_ratCast (d : ℕ) (l u : ℕ → ℚ) :
    coeffVariationBudget d (fun j => (l j : K)) (fun j => (u j : K)) =
      coeffVariationBudget d l u := by
  simp [coeffVariationBudget]

end Rational

end RKCert.ReviewedNative.PolynomialCertificate
