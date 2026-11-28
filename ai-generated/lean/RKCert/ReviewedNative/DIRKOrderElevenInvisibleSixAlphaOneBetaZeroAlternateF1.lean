import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneBetaZeroAlternateF1

variable {K : Type*} [CommRing K]

theorem specialized_affinity_product (a r s c1 c2 : K)
    (hc : 80*c1 = 96*s + 75*a*(c2-a)) :
    80*(a*r^2 - (2*s+c1)*r + 3*(c2-a)*s) =
      (16*r-15*(c2-a))*(5*a*r-16*s) := by
  linear_combination -r*hc

theorem only_alternate_root [IsDomain K] {a r s c1 c2 : K}
    (hc : 80*c1 = 96*s + 75*a*(c2-a))
    (he : 16*r ≠ 15*(c2-a))
    (h : a*r^2 - (2*s+c1)*r + 3*(c2-a)*s = 0) :
    5*a*r = 16*s := by
  have hp := specialized_affinity_product a r s c1 c2 hc
  rw [h, mul_zero] at hp
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp.symm).resolve_left (sub_ne_zero.mpr he))

theorem alternate_eliminants_scaled {a s c0 c1 c2 : K}
    (h0 : c0 = a*s) (h1 : 192*s = 25*a*(a+c2))
    (h2 : 40*c1 = 336*s - 75*a^2) :
    (25*a^3+25*c2*a^2-192*c0 = 0) ∧
    (5*(15*c2*a^2-8*c1*a-48*c0) = 0) := by
  have h3 : 25*a^3+25*c2*a^2-192*c0 = 0 := by
    linear_combination -a*h1 - 192*h0
  refine ⟨h3, ?_⟩
  linear_combination 3*h3 - a*h2 + 336*h0

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneBetaZeroAlternateF1

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneBetaZeroAlternateF1
#print axioms specialized_affinity_product
#print axioms only_alternate_root
#print axioms alternate_eliminants_scaled
