import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneBetaZeroAlternateF2

variable {K : Type*} [CommRing K]

theorem specialized_affinity_product (a r s c1 c2 : K)
    (hc : c1 = s + a*(c2-a)) :
    a*r^2 - (2*s+c1)*r + 3*c2*s - 3*a*s =
      (r-(c2-a))*(a*r-3*s) := by
  rw [hc]
  ring

theorem only_alternate_root [IsDomain K] {a r s c1 c2 : K}
    (hc : c1 = s + a*(c2-a)) (he : r ≠ c2-a)
    (h : a*r^2 - (2*s+c1)*r + 3*c2*s - 3*a*s = 0) :
    a*r = 3*s := by
  rw [specialized_affinity_product a r s c1 c2 hc] at h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr he))

theorem forbidden_old_determinant_factor [IsDomain K] {n k a c2 s : K}
    (hn : n ≠ 0) (h : n = k*(a^2-a*c2+3*s)^2) :
    a^2-a*c2+3*s ≠ 0 := by
  intro hz
  apply hn
  simp [h, hz]

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneBetaZeroAlternateF2

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneBetaZeroAlternateF2
#print axioms specialized_affinity_product
#print axioms only_alternate_root
#print axioms forbidden_old_determinant_factor
