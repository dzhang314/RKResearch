module

public import RKCert.ReviewedNative.PolynomialCertificateBox
public import RKCert.ReviewedNative.PolynomialCertificateDyadicCover
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Order.Interval.Set.Basic

import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact rational coefficient tables for a two-parameter chart

Four coefficient columns represent 1,s,t,st. A Horner recurrence computes
the Hasse coefficients of any translate and is proved equal to polynomial
Taylor coefficients. Exact comparisons at the four rational corners lift
to every field-valued point of a closed dyadic rectangle.
-/

namespace RKCert.ReviewedNative.PolynomialCertificate

open Polynomial
open scoped Polynomial

section Horner

variable {R : Type*} [CommSemiring R]

/-- Ascending-power coefficients, including any trailing zeros. -/
noncomputable def listPolynomial : List R → R[X]
  | [] => 0
  | a :: cs => C a + X * listPolynomial cs

/-- Kernel-reducible Horner algorithm for every Taylor coefficient, with
the normalization of Hasse derivatives. -/
def taylorEntry (x : R) : List R → ℕ → R
  | [] => fun _ => 0
  | a :: cs => fun j =>
    match j with
    | 0 => a + x * taylorEntry x cs 0
    | k + 1 => taylorEntry x cs k + x * taylorEntry x cs (k + 1)

theorem listPolynomial_taylor_coeff (cs : List R) (x : R) (j : ℕ) :
    ((listPolynomial cs).taylor x).coeff j = taylorEntry x cs j := by
  induction cs generalizing j with
  | nil => simp only [listPolynomial, map_zero, coeff_zero, taylorEntry]
  | cons a cs ih =>
    cases j with
    | zero =>
      simp only [listPolynomial, map_add, taylor_C, taylor_mul, taylor_X, add_mul,
        coeff_add, coeff_C_zero, coeff_X_mul_zero, coeff_C_mul, zero_add, taylorEntry, ih]
    | succ k =>
      simp only [listPolynomial, map_add, taylor_C, taylor_mul, taylor_X, add_mul,
        coeff_add, coeff_C_succ, zero_add, coeff_X_mul, coeff_C_mul, taylorEntry, ih,
        Nat.succ_eq_add_one]

theorem taylorEntry_zero_of_length_le (cs : List R) (x : R) {j : ℕ} (h : cs.length ≤ j) :
    taylorEntry x cs j = 0 := by
  induction cs generalizing j with
  | nil => rfl
  | cons a cs ih =>
    cases j with
    | zero => simp at h
    | succ k =>
      have h' : cs.length ≤ k := by simpa using h
      simp only [taylorEntry, ih h', ih (Nat.le.step h'), mul_zero, add_zero]

/-- The scalar part of a general biaffine chart. -/
def biForm (a b c d s t : R) : R := a + s * b + t * c + (s * t) * d

end Horner

structure RationalColumns where
  base : List ℚ
  inS : List ℚ
  inT : List ℚ
  inST : List ℚ
  deriving Repr

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem taylorEntry_ratCast (cs : List ℚ) (x : ℚ) (j : ℕ) :
    taylorEntry (x : K) (cs.map (fun a : ℚ => (a : K))) j = ((taylorEntry (R := ℚ) x cs j : ℚ) : K) := by
  induction cs generalizing j with
  | nil => simp [taylorEntry]
  | cons a cs ih =>
    cases j <;> simp [taylorEntry, ih]

noncomputable def rationalChart (v : RationalColumns) (s t : K) : K[X] :=
  let liftPoly := fun c : List ℚ => listPolynomial (c.map (fun a : ℚ => (a : K)))
  liftPoly v.base + C s * liftPoly v.inS + C t * liftPoly v.inT + C (s * t) * liftPoly v.inST

def chartJet (v : RationalColumns) (x : ℚ) (j : ℕ) (s t : K) : K :=
  biForm ((taylorEntry (R := ℚ) x v.base j : ℚ) : K) ((taylorEntry (R := ℚ) x v.inS j : ℚ) : K)
    ((taylorEntry (R := ℚ) x v.inT j : ℚ) : K) ((taylorEntry (R := ℚ) x v.inST j : ℚ) : K) s t

theorem rationalChart_taylor_coeff (v : RationalColumns) (x : ℚ) (j : ℕ) (s t : K) :
    ((rationalChart v s t).taylor (x : K)).coeff j = chartJet v x j s t := by
  simp only [rationalChart, chartJet, biForm, map_add, taylor_mul, taylor_C, coeff_add,
    coeff_C_mul, listPolynomial_taylor_coeff, taylorEntry_ratCast]

theorem rationalChart_natDegree_le (v : RationalColumns) (d : ℕ) (s t : K)
    (h₀ : v.base.length ≤ d + 1) (h₁ : v.inS.length ≤ d + 1)
    (h₂ : v.inT.length ≤ d + 1) (h₃ : v.inST.length ≤ d + 1) :
    (rationalChart v s t).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  have hj' : d + 1 ≤ j := Nat.succ_le_of_lt hj
  have hh := rationalChart_taylor_coeff v 0 j s t
  simpa [chartJet, biForm, taylorEntry_zero_of_length_le _ _ (h₀.trans hj'),
    taylorEntry_zero_of_length_le _ _ (h₁.trans hj'),
    taylorEntry_zero_of_length_le _ _ (h₂.trans hj'),
    taylorEntry_zero_of_length_le _ _ (h₃.trans hj')] using hh

theorem chartJet_ratCast (v : RationalColumns) (x : ℚ) (j : ℕ) (s t : ℚ) :
    chartJet v x j (s : K) (t : K) = ((chartJet (K := ℚ) v x j s t : ℚ) : K) := by
  simp [chartJet, biForm]

private theorem biForm_mix_first (a b c d l u t z : K) :
    biForm a b c d (mix l u z) t = mix (biForm a b c d l t) (biForm a b c d u t) z := by
  unfold biForm mix
  ring

private theorem biForm_mix_second (a b c d s l u z : K) :
    biForm a b c d s (mix l u z) = mix (biForm a b c d s l) (biForm a b c d s u) z := by
  unfold biForm mix
  ring

theorem biForm_mem_Icc_of_four_corners (a b c d : K)
    {l₁ u₁ l₂ u₂ s t lo hi : K} (hs : s ∈ Set.Icc l₁ u₁) (ht : t ∈ Set.Icc l₂ u₂)
    (hll : biForm a b c d l₁ l₂ ∈ Set.Icc lo hi)
    (hlu : biForm a b c d l₁ u₂ ∈ Set.Icc lo hi)
    (hul : biForm a b c d u₁ l₂ ∈ Set.Icc lo hi)
    (huu : biForm a b c d u₁ u₂ ∈ Set.Icc lo hi) : biForm a b c d s t ∈ Set.Icc lo hi := by
  obtain ⟨z, hz, hsz⟩ := exists_unit_mix hs
  obtain ⟨w, hw, htw⟩ := exists_unit_mix ht
  have hl : biForm a b c d l₁ t ∈ Set.Icc lo hi := by
    rw [htw, biForm_mix_second]
    exact mixClosed_Icc lo hi hw.1 hw.2 hll hlu
  have hu : biForm a b c d u₁ t ∈ Set.Icc lo hi := by
    rw [htw, biForm_mix_second]
    exact mixClosed_Icc lo hi hw.1 hw.2 hul huu
  rw [hsz, biForm_mix_first]
  exact mixClosed_Icc lo hi hz.1 hz.2 hl hu

def DyadicRect.left (r : DyadicRect) : ℚ := gridCoord (2 ^ r.xDepth) r.xIndex

def DyadicRect.right (r : DyadicRect) : ℚ := gridCoord (2 ^ r.xDepth) (r.xIndex + 1)

def DyadicRect.bottom (r : DyadicRect) : ℚ := gridCoord (2 ^ r.yDepth) r.yIndex

def DyadicRect.top (r : DyadicRect) : ℚ := gridCoord (2 ^ r.yDepth) (r.yIndex + 1)

/-- A directly decidable comparison of exact rational corner values. -/
abbrev chartJetCornersIn (v : RationalColumns) (r : DyadicRect) (x : ℚ)
    (j : ℕ) (lo hi : ℚ) : Prop :=
  chartJet v x j r.left r.bottom ∈ Set.Icc lo hi ∧
  chartJet v x j r.left r.top ∈ Set.Icc lo hi ∧
  chartJet v x j r.right r.bottom ∈ Set.Icc lo hi ∧
  chartJet v x j r.right r.top ∈ Set.Icc lo hi

private theorem chartJet_Icc_ratCast (v : RationalColumns) (x : ℚ) (j : ℕ)
    {s t lo hi : ℚ} (h : chartJet v x j s t ∈ Set.Icc lo hi) :
    chartJet v x j (s : K) (t : K) ∈ Set.Icc (lo : K) (hi : K) := by
  rw [chartJet_ratCast]
  exact ⟨Rat.cast_le.mpr h.1, Rat.cast_le.mpr h.2⟩

private theorem gridCoord_ratCast (den i : ℕ) :
    ((gridCoord (K := ℚ) den i : ℚ) : K) = gridCoord (K := K) den i := by
  simp [gridCoord]

theorem rationalChart_coeff_mem_of_corners (v : RationalColumns) (r : DyadicRect) (x : ℚ)
    (j : ℕ) (lo hi : ℚ) (corners : chartJetCornersIn v r x j lo hi)
    {s t : K} (hr : InDyadicRect r s t) :
    ((rationalChart v s t).taylor (x : K)).coeff j ∈ Set.Icc (lo : K) (hi : K) := by
  have hs : s ∈ Set.Icc (r.left : K) (r.right : K) := by
    simpa only [DyadicRect.left, DyadicRect.right, gridCoord_ratCast] using hr.1
  have ht : t ∈ Set.Icc (r.bottom : K) (r.top : K) := by
    simpa only [DyadicRect.bottom, DyadicRect.top, gridCoord_ratCast] using hr.2
  rw [rationalChart_taylor_coeff]
  apply biForm_mem_Icc_of_four_corners _ _ _ _ hs ht
  · exact chartJet_Icc_ratCast v x j corners.1
  · exact chartJet_Icc_ratCast v x j corners.2.1
  · exact chartJet_Icc_ratCast v x j corners.2.2.1
  · exact chartJet_Icc_ratCast v x j corners.2.2.2

end RKCert.ReviewedNative.PolynomialCertificate
