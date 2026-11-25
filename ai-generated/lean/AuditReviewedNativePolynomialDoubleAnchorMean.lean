import RKCert.ReviewedNative.PolynomialDoubleAnchorMean
import RKCert.ReviewedNative.PositiveIntervalGrid19
import Mathlib.Tactic.NormNum

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.AnchorMean RKCert.ReviewedNative.PositiveRule19

variable {K : Type*} [Field K] [CharZero K]

example {q : K[X]} {u : K} (hu : u ≠ 0)
    (first : integral 0 u (X * q) = 0)
    (second : integral 0 u (X ^ 2 * q) = 0) :
    ∃ h : K[X], formalPrimitive (anchorPair u * q) = anchorPair u ^ 2 * h ∧
      integral 0 u (X ^ 2 * h) = 0 := by
  obtain ⟨h, factor, mean⟩ := exists_anchored_quotient_mean hu
    (by simpa only [integral_zero_left] using first)
    (by simpa only [integral_zero_left] using second)
  exact ⟨h, factor, by simpa only [integral_zero_left] using mean⟩

example {q : K[X]} {u : K} (mq : q.Monic) (qd : q.natDegree = 3)
    (hu : u ≠ 0) (first : integral 0 u (X * q) = 0)
    (second : integral 0 u (X ^ 2 * q) = 0) :
    ∃ H : K[X], H.Monic ∧ H.natDegree = 2 ∧
      formalPrimitive (anchorPair u * q) = C ((6 : K)⁻¹) * (anchorPair u ^ 2 * H) ∧
      integral 0 u (X ^ 2 * H) = 0 ∧
      q = C ((6 : K)⁻¹) * (2 * (anchorPair u).derivative * H + anchorPair u * H.derivative) := by
  obtain ⟨H, hm, d, factor, mean⟩ := exists_monic_anchored_quotient_mean mq hu
    (by simpa only [integral_zero_left] using first)
    (by simpa only [integral_zero_left] using second)
  have cubicFactor :
      formalPrimitive (anchorPair u * q) = C ((6 : K)⁻¹) * (anchorPair u ^ 2 * H) := by
    have six : ((3 + 3 : ℕ) : K) = (6 : K) := by norm_num
    simpa only [qd, six] using factor
  exact ⟨H, hm, by omega, cubicFactor, by simpa only [integral_zero_left] using mean,
    reconstruct_of_anchored_primitive cubicFactor⟩

#print axioms RKCert.ReviewedNative.AnchorMean.exists_anchored_quotient_mean
#print axioms RKCert.ReviewedNative.AnchorMean.exists_monic_anchored_quotient_mean
#print axioms RKCert.ReviewedNative.AnchorMean.reconstruct_of_anchored_primitive
