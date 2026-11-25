module

public import RKCert.ReviewedNative.PolynomialCertificateIntegerChart
public import RKCert.ReviewedNative.PolynomialCertificateDescartes
public import Mathlib.Algebra.Ring.Parity

@[expose] public section

/-! # Sound Descartes budgets from integer chart corners

Above-threshold translations keep signs; below-threshold translations
reverse precisely the odd coefficient intervals. Finite sign words may
contain zeros, including identically zero and ambiguous coefficients. -/

namespace RKCert.ReviewedNative.PolynomialCertificate

open Polynomial
open scoped Polynomial

def orientedInterval (below : Bool) (j : ℕ) (q : IntegerQuad) : ℤ × ℤ :=
  if below then (if Even j then (q.low, q.high) else (-q.high, -q.low))
  else (q.low, q.high)

def integerBounds (v : IntegerColumns) (width : ℕ) (z d : ℤ) (r : DyadicRect)
    (below : Bool) (j : ℕ) : ℤ × ℤ := orientedInterval below j (integerQuad v width z d r j)

def integerBudget (v : IntegerColumns) (width degree : ℕ) (z d : ℤ) (r : DyadicRect)
    (below : Bool) : ℕ :=
  coeffVariationBudget degree (fun j => (integerBounds v width z d r below j).1)
    (fun j => (integerBounds v width z d r below j).2)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

@[simp] theorem allowedSigns_intCast (a b : ℤ) :
    allowedSigns (a : K) (b : K) = allowedSigns a b := by simp [allowedSigns]

@[simp] theorem coeffVariationBudget_intCast (degree : ℕ) (lo hi : ℕ → ℤ) :
    coeffVariationBudget degree (fun j => (lo j : K)) (fun j => (hi j : K)) =
    coeffVariationBudget degree lo hi := by simp [coeffVariationBudget]

private theorem signVariations_le_integer_bounds {p : K[X]} {degree : ℕ}
    (hd : p.natDegree ≤ degree) (bounds : ℕ → ℤ × ℤ)
    (h : ∀ j ≤ degree, p.coeff j ∈ Set.Icc ((bounds j).1 : K) ((bounds j).2 : K)) :
    p.signVariations ≤ coeffVariationBudget degree (fun j => (bounds j).1) (fun j => (bounds j).2) := by
  calc
    p.signVariations ≤ coeffVariationBudget degree (fun j => ((bounds j).1 : K))
        (fun j => ((bounds j).2 : K)) := signVariations_le_coeffVariationBudget hd h
    _ = _ := coeffVariationBudget_intCast degree _ _

theorem above_scaled_variations_le (v : IntegerColumns) (width degree : ℕ) (hw : v.Within width)
    (z d : ℤ) (hd : 0 < d) (r : DyadicRect) {s t : K} (hr : InDyadicRect r s t)
    (hdeg : (integerScaledChart v width d r s t).natDegree ≤ degree) :
    (abovePoly (integerScaledChart v width d r s t) (((z : ℚ) / d : ℚ) : K)).signVariations ≤
      integerBudget v width degree z d r false := by
  let p := integerScaledChart v width d r s t
  let x : K := (((z : ℚ) / d : ℚ) : K)
  apply signVariations_le_integer_bounds (p := abovePoly p x)
    (by simpa only [abovePoly_natDegree] using hdeg)
    (integerBounds v width z d r false)
  intro j _
  exact integerScaledChart_taylor_coeff v width hw z d hd r j hr

theorem below_scaled_variations_le (v : IntegerColumns) (width degree : ℕ) (hw : v.Within width)
    (z d : ℤ) (hd : 0 < d) (r : DyadicRect) {s t : K} (hr : InDyadicRect r s t)
    (hdeg : (integerScaledChart v width d r s t).natDegree ≤ degree) :
    (belowPoly (integerScaledChart v width d r s t) (((z : ℚ) / d : ℚ) : K)).signVariations ≤
      integerBudget v width degree z d r true := by
  let p := integerScaledChart v width d r s t
  let x : K := (((z : ℚ) / d : ℚ) : K)
  apply signVariations_le_integer_bounds (p := belowPoly p x)
    (by simpa only [belowPoly_natDegree] using hdeg)
    (integerBounds v width z d r true)
  intro j _
  let q := integerQuad v width z d r j
  have hc : (p.taylor x).coeff j ∈ Set.Icc (q.low : K) (q.high : K) :=
    integerScaledChart_taylor_coeff v width hw z d hd r j hr
  have eqn : (belowPoly p x).coeff j = (p.taylor x).coeff j * (-1 : K) ^ j := by
    rw [belowPoly_coeff, taylor_coeff]
  change (belowPoly p x).coeff j ∈ Set.Icc ((orientedInterval true j q).1 : K)
    ((orientedInterval true j q).2 : K)
  rw [eqn]
  by_cases hj : Even j
  · simpa only [orientedInterval, if_true, if_pos hj, hj.neg_one_pow, mul_one] using hc
  · have hodd : (-1 : K) ^ j = -1 := (Nat.not_even_iff_odd.mp hj).neg_one_pow
    simp only [orientedInterval, if_true, if_neg hj, Int.cast_neg, hodd, mul_neg_one]
    exact ⟨neg_le_neg hc.2, neg_le_neg hc.1⟩

end RKCert.ReviewedNative.PolynomialCertificate
