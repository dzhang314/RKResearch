module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorLocalizer

import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Closed ordered-field ratio transport for the literal three-change boxes

These are exactly the four interval formulas in the existing checker.
The only strict guard is a nonzero endpoint denominator for the side at
which the selected actual test stops. No field-valued samples are tested.
-/
namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem left_scale_pos_closed {s d : K} (hs : s ∈ Set.Icc 0 1) (d0 : 0 < d) :
    0 < threeInteriorLeftScale s d := by
  rcases eq_or_lt_of_le hs.1 with z | h
  · rw [← z, threeInteriorLeftScale, sub_zero, one_mul, zero_add]
    exact d0
  · exact add_pos_of_pos_of_nonneg h (mul_nonneg (sub_nonneg.mpr hs.2) d0.le)

private theorem left_gamma_anti_density {s t d : K} (hs : s ∈ Set.Icc 0 1)
    (ht : t ∈ Set.Icc 0 1) (st : s ≤ t) (d0 : 0 < d) :
    threeInteriorLeftGamma t d ≤ threeInteriorLeftGamma s d := by
  unfold threeInteriorLeftGamma
  apply (div_le_div_iff₀ (left_scale_pos_closed ht d0) (left_scale_pos_closed hs d0)).2
  unfold threeInteriorLeftScale
  have h : 0 ≤ (t-s)*d := mul_nonneg (sub_nonneg.mpr st) d0.le
  nlinarith only [h]

private theorem left_gamma_mono_stop {s d e : K} (hs : s ∈ Set.Icc 0 1)
    (d0 : 0 < d) (de : d ≤ e) :
    threeInteriorLeftGamma s d ≤ threeInteriorLeftGamma s e := by
  unfold threeInteriorLeftGamma
  apply (div_le_div_iff₀ (left_scale_pos_closed hs d0) (left_scale_pos_closed hs (d0.trans_le de))).2
  unfold threeInteriorLeftScale
  have h : 0 ≤ s*(1-s)*(e-d) :=
    mul_nonneg (mul_nonneg hs.1 (sub_nonneg.mpr hs.2)) (sub_nonneg.mpr de)
  nlinarith only [h]

theorem threeInterior_leftGamma_bounds {sl su dl du s d : K}
    (sl0 : 0 ≤ sl) (su1 : su ≤ 1) (dl0 : 0 < dl)
    (hs : s ∈ Set.Icc sl su) (hd : d ∈ Set.Icc dl du) :
    threeInteriorLeftGamma s d ∈
      Set.Icc (threeInteriorLeftGamma su dl) (threeInteriorLeftGamma sl du) := by
  have L : sl ∈ Set.Icc (0:K) 1 := ⟨sl0, (hs.1.trans hs.2).trans su1⟩
  have S : s ∈ Set.Icc (0:K) 1 := ⟨sl0.trans hs.1, hs.2.trans su1⟩
  have U : su ∈ Set.Icc (0:K) 1 := ⟨S.1.trans hs.2, su1⟩
  have d0 : 0 < d := dl0.trans_le hd.1
  refine ⟨?_, ?_⟩
  · exact (left_gamma_mono_stop U dl0 hd.1).trans (left_gamma_anti_density S U hs.2 d0)
  · exact (left_gamma_anti_density L S hs.1 d0).trans (left_gamma_mono_stop L d0 hd.2)

theorem threeInterior_leftRoot_bounds {xl xu dl du x d : K}
    (xl0 : 0 ≤ xl) (dl0 : 0 < dl) (hx : x ∈ Set.Icc xl xu) (hd : d ∈ Set.Icc dl du) :
    threeInteriorLeftRoot d x ∈
      Set.Icc (threeInteriorLeftRoot du xl) (threeInteriorLeftRoot dl xu) := by
  have d0 : 0 < d := dl0.trans_le hd.1
  have xu0 : 0 ≤ xu := (xl0.trans hx.1).trans hx.2
  change xl/du ≤ x/d ∧ x/d ≤ xu/dl
  exact ⟨(div_le_div_of_nonneg_left xl0 d0 hd.2).trans
           ((div_le_div_iff_of_pos_right d0).2 hx.1),
         ((div_le_div_iff_of_pos_right d0).2 hx.2).trans
           (div_le_div_of_nonneg_left xu0 dl0 hd.1)⟩

private theorem right_gamma_anti_both {s t d e : K}
    (t1 : t ≤ 1) (e1 : e ≤ 1) (st : s ≤ t) (de : d ≤ e) :
    threeInteriorRightGamma t e ≤ threeInteriorRightGamma s d := by
  unfold threeInteriorRightGamma
  calc
    (1-t)*(1-e) ≤ (1-s)*(1-e) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_left st 1) (sub_nonneg.mpr e1)
    _ ≤ (1-s)*(1-d) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left de 1) (sub_nonneg.mpr (st.trans t1))

theorem threeInterior_rightGamma_bounds {sl su dl du s d : K}
    (su1 : su ≤ 1) (du1 : du ≤ 1)
    (hs : s ∈ Set.Icc sl su) (hd : d ∈ Set.Icc dl du) :
    threeInteriorRightGamma s d ∈ Set.Icc
      (threeInteriorRightGamma su du) (threeInteriorRightGamma sl dl) :=
  ⟨right_gamma_anti_both su1 du1 hs.2 hd.2,
    right_gamma_anti_both (hs.2.trans su1) (hd.2.trans du1) hs.1 hd.1⟩

private theorem right_root_mono_site {x y d : K} (d1 : d < 1) (xy : x ≤ y) :
    threeInteriorRightRoot d x ≤ threeInteriorRightRoot d y := by
  unfold threeInteriorRightRoot
  exact (div_le_div_iff_of_pos_right (sub_pos.mpr d1)).2 (sub_le_sub_right xy d)

private theorem right_root_anti_stop {x d e : K} (x1 : x ≤ 1) (e1 : e < 1) (de : d ≤ e) :
    threeInteriorRightRoot e x ≤ threeInteriorRightRoot d x := by
  unfold threeInteriorRightRoot
  apply (div_le_div_iff₀ (sub_pos.mpr e1) (sub_pos.mpr (de.trans_lt e1))).2
  have h : 0 ≤ (1-x)*(e-d) := mul_nonneg (sub_nonneg.mpr x1) (sub_nonneg.mpr de)
  nlinarith only [h]

theorem threeInterior_rightRoot_bounds {xl xu dl du x d : K}
    (xu1 : xu ≤ 1) (du1 : du < 1) (hx : x ∈ Set.Icc xl xu) (hd : d ∈ Set.Icc dl du) :
    threeInteriorRightRoot d x ∈
      Set.Icc (threeInteriorRightRoot du xl) (threeInteriorRightRoot dl xu) := by
  have xl1 : xl ≤ 1 := (hx.1.trans hx.2).trans xu1
  have d1 : d < 1 := hd.2.trans_lt du1
  exact ⟨(right_root_anti_stop xl1 du1 hd.2).trans (right_root_mono_site d1 hx.1),
    (right_root_mono_site d1 hx.2).trans (right_root_anti_stop xu1 d1 hd.1)⟩

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
