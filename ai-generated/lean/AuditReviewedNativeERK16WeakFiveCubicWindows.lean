import RKCert.ReviewedNative.ERKOrder16WeakFiveCubicWindows
import RKCert.ReviewedNative.CubicAnchoredCutoff

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.WeakFive16 RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.CubicEnd RKCert.ReviewedNative.AnchorMean

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

example {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (deg : q.natDegree = 3) :
    OrientedCubicWindow (q*C q.leadingCoeff⁻¹) (c 1) (c 2) (c 3) (c 4) ∨
      OrientedCubicWindow (cubicStar (q*C q.leadingCoeff⁻¹))
        (1-c 4) (1-c 3) (1-c 2) (1-c 1) :=
  M.oriented_cubic_window deg

-- Exact typed connection to the checked no-grid anchored cutoff.
example {q : K[X]} {u a h z : K} (O : OrientedCubicWindow q u a h z) :
    u < (11 : K)/12 ∧ 1-z < (11 : K)/12 ∧
      ∀ x : K, (14 : K)/15 ≤ x →
        0 < q.eval x ∧ 0 < (formalPrimitive (anchorPair u*q)).eval x := by
  have W := O.window
  have R := W.reflected
  exact positive_of_monic_cubic_end_moments W.monic W.degree O.leftPositive
    O.rightPositive W.uOff.2 O.overlap O.orientation
    (by simpa only [integral_zero_left] using W.leftFirst)
    (by simpa only [integral_zero_left] using W.leftSecond)
    (by simpa only [integral_zero_left, cubicStar, reflectCubic] using R.leftFirst)
    (by simpa only [integral_zero_left, cubicStar, reflectCubic] using R.leftSecond)

#print axioms RKCert.ReviewedNative.FiniteOrderedSigns.HasAlternationsOn.of_mul_sq
#print axioms RKCert.ReviewedNative.WeakFive16.CubicWindow.reflected
#print axioms RKCert.ReviewedNative.WeakFive16.CubicWindow.paid_lengths
#print axioms RKCert.ReviewedNative.WeakFive16.Moments.oriented_cubic_window
