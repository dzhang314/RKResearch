module

public import RKCert.ReviewedNative.WeakFiveSoleOuterGlue

@[expose] public section

/-! # Complete native scalar endpoint for the actual sole outer clock

The common classifier is the only geometric premise. This endpoint spends
no reference-chart boxes and no other weak-five or weak-four terminal theorem.
-/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.WeakFive16
open RKCert.ReviewedNative.OrderedRootGapSaturation
open RKCert.ReviewedNative.WeakFiveCrossedPositiveTail
open scoped Polynomial

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The proved ordered-field terminal. It consumes the actual paid M
and the sole-outer geometric output, not a supplied quartic factorization. -/
theorem no_actual_weakfive_sole_outer {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (H : SoleOuter c) : False := by
  obtain ⟨E,G⟩ := self_gap_complete_extension q
  let C' : Fin 5 → E.carrier := fun i => E.embed (c i)
  let Q := q.map E.embed
  let p := monicProfile Q
  have actual : Moments Q (Z.map E.embed) C' := moments_along_field E.embed M
  have cn : Q.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr actual.qNonzero)
  have normalized : Moments p (Z.map E.embed) C' := moments_scale_nonzero actual cn
  have pm : p.Monic := monicProfile_monic Q actual.qNonzero
  have pg : GapComplete p := G.scale cn
  have keep {i : Fin 5} (h : MarkInterior c i) : MarkInterior C' i :=
    ⟨by simpa only [C',map_zero] using E.mono h.1,
     by simpa only [C',map_one] using E.mono h.2⟩
  rcases H with ⟨z,u,a,h,uh⟩ | ⟨u,a,h,z,az⟩
  · have zn : C' 4 < 0 := by simpa only [C',map_zero] using E.mono z
    exact sole_outer_words_impossible
      (exterior_left_words normalized pm zn (keep u) (keep a) (keep h) (E.mono uh)) pg
  · have un : 1 < C' 1 := by simpa only [C',map_one] using E.mono u
    exact sole_outer_words_impossible
      (exterior_right_words normalized pm un (keep a) (keep h) (keep z) (E.mono az))
      (gap_complete_flip pg)

/-- Now only the three independent inner, three-change, and negative-tail
consumers remain on the actual native scalar path. -/
theorem actual_weak_five_without_outer {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) : SoleInner q c ∨ ThreeInterior q c ∨ CrossedNegative q Z c :=
  (actual_weak_five_remaining_sectors M).resolve_left (no_actual_weakfive_sole_outer M)

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
