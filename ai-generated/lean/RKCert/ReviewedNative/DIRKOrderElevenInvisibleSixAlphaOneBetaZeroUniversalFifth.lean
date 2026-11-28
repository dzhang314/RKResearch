import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneBetaZeroUniversalFifth

variable {K : Type*} [CommRing K]

theorem positive_monomial_coefficient [IsDomain K] {a z s : K}
    (hz : z ≠ 0) (hs : s ≠ 0) (h : a * (-(z*s)) = 0) : a = 0 := by
  exact (mul_eq_zero.mp h).resolve_right (neg_ne_zero.mpr (mul_ne_zero hz hs))

theorem constant_monomial_old_coefficients {r s z : K}
    (h3 : 4*r = 3*(r-z)) (h2 : 2*s = s-r*z) :
    r = -3*z ∧ s = 3*z^2 := by
  have hr : r = -3*z := by linear_combination h3
  refine ⟨hr, ?_⟩
  rw [hr] at h2
  linear_combination h2

theorem lost_ratio_monic_scale {a r s : K}
    (h : a*(r^2-3*s)+4*r*s^2=0) :
    (a*r)^2+4*s^2*(a*r)-3*s*a^2=0 := by
  linear_combination a * h

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneBetaZeroUniversalFifth

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneBetaZeroUniversalFifth
#print axioms positive_monomial_coefficient
#print axioms constant_monomial_old_coefficients
#print axioms lost_ratio_monic_scale
