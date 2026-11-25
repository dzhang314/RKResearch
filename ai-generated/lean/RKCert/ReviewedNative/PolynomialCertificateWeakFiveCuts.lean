module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCells
public import RKCert.ReviewedNative.PolynomialCertificateRationalChart

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Actual weak-five centered chart: four strict Laguerre exclusions

Only the four type-2 cells of the published weak-five four-change table
are treated here. The factor four clears all rational coefficients from
the centered chart. No ordinary weak-four family is used.
-/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial
open scoped Polynomial

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

/-- Columns of four times the paper's 2145*T_y in the order 1,s,t,st. -/
def centeredColumns : RationalColumns where
  base := [-15, 0, -15, 0, 3135, 0, -10725, 0, 8580]
  inS := [75, 0, -2025, 0, 7425, 0, -6435]
  inT := [0, -525, 0, 5775, 0, -15015, 0, 10725]
  inST := [0, 525, 0, -5775, 0, 15015, 0, -10725]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

noncomputable def sixthColumn : K[X] := 429 * X ^ 6 - 495 * X ^ 4 + 135 * X ^ 2 - 5

noncomputable def seventhColumn : K[X] :=
  715 * X ^ 7 - 1001 * X ^ 5 + 385 * X ^ 3 - 35 * X

/-- This is 4 times 3*(X-D)*A7 - 5*lambda*A6, with
D=-(5/4)*(1-s)*t and lambda=(15*s-3)/20. -/
noncomputable def centeredPolynomial (s t : K) : K[X] :=
  12 * X * seventhColumn + C (15 * (1 - s) * t) * seventhColumn
    - C (15 * s - 3) * sixthColumn

theorem chart_eq_centeredPolynomial (s t : K) :
    rationalChart centeredColumns s t = centeredPolynomial s t := by
  simp only [rationalChart, centeredColumns, centeredPolynomial, sixthColumn, seventhColumn,
    List.map_cons, List.map_nil, listPolynomial, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_neg,
    map_mul, map_sub, map_neg, map_one, map_zero, map_ofNat]
  ring

theorem centeredChart_natDegree (s t : K) : (rationalChart centeredColumns s t).natDegree = 8 := by
  have hb := rationalChart_natDegree_le centeredColumns 8 s t
    (by decide) (by decide) (by decide) (by decide)
  have h₀ : taylorEntry 0 centeredColumns.base 8 = 8580 := by decide +kernel
  have h₁ : taylorEntry 0 centeredColumns.inS 8 = 0 := by decide +kernel
  have h₂ : taylorEntry 0 centeredColumns.inT 8 = 0 := by decide +kernel
  have h₃ : taylorEntry 0 centeredColumns.inST 8 = 0 := by decide +kernel
  have he : (rationalChart centeredColumns s t).coeff 8 = (8580 : K) := by
    simpa [chartJet, biForm, h₀, h₁, h₂, h₃] using
      rationalChart_taylor_coeff centeredColumns 0 8 s t
  exact le_antisymm hb (le_natDegree_of_ne_zero (by rw [he]; norm_num))

abbrev CutRow.enclosesCorners (r : CutRow) : Prop :=
  chartJetCornersIn centeredColumns r.rect r.threshold 0 r.lo₀ r.hi₀ ∧
  chartJetCornersIn centeredColumns r.rect r.threshold 1 r.lo₁ r.hi₁ ∧
  chartJetCornersIn centeredColumns r.rect r.threshold 2 r.lo₂ r.hi₂

theorem cut12_encloses : cut12.enclosesCorners := by decide +kernel
theorem cut16_encloses : cut16.enclosesCorners := by decide +kernel
theorem cut42_encloses : cut42.enclosesCorners := by decide +kernel
theorem cut44_encloses : cut44.enclosesCorners := by decide +kernel

theorem CutRow.not_splits (r : CutRow) (accepted : r.ok) (hc : r.enclosesCorners)
    {s t : K} (inside : InDyadicRect r.rect s t) : ¬(centeredPolynomial s t).Splits := by
  rw [← chart_eq_centeredPolynomial]
  exact not_splits_of_laguerre_interval (centeredChart_natDegree s t)
    (by decide) (r.threshold : K)
    (rationalChart_coeff_mem_of_corners centeredColumns r.rect _ _ _ _ hc.1 inside)
    (rationalChart_coeff_mem_of_corners centeredColumns r.rect _ _ _ _ hc.2.1 inside)
    (rationalChart_coeff_mem_of_corners centeredColumns r.rect _ _ _ _ hc.2.2 inside)
    (laguerreIntervalCut_ratCast (K := K) accepted)

/-- Every point, including all seams, of the four displayed parameter
rectangles has a centered polynomial that does not fully split over K. -/
theorem not_splits_in_four_cut_cells {s t : K}
    (inside : InDyadicRect cut12.rect s t ∨ InDyadicRect cut16.rect s t ∨
      InDyadicRect cut42.rect s t ∨ InDyadicRect cut44.rect s t) :
    ¬(centeredPolynomial s t).Splits := by
  rcases inside with h | h | h | h
  · exact cut12.not_splits cut12_ok cut12_encloses h
  · exact cut16.not_splits cut16_ok cut16_encloses h
  · exact cut42.not_splits cut42_ok cut42_encloses h
  · exact cut44.not_splits cut44_ok cut44_encloses h

theorem no_eight_sites_in_four_cut_cells {s t : K}
    (inside : InDyadicRect cut12.rect s t ∨ InDyadicRect cut16.rect s t ∨
      InDyadicRect cut42.rect s t ∨ InDyadicRect cut44.rect s t)
    {β : Fin 8 → K} (hi : Function.Injective β)
    (hr : ∀ i, (centeredPolynomial s t).IsRoot (β i)) : False := by
  have hd : (centeredPolynomial s t).natDegree = 8 := by
    rw [← chart_eq_centeredPolynomial, centeredChart_natDegree]
  have hp : centeredPolynomial s t ≠ 0 := by
    intro h
    simp [h] at hd
  exact not_splits_in_four_cut_cells inside (splits_of_full_site_tuple hp hd hi hr)

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
