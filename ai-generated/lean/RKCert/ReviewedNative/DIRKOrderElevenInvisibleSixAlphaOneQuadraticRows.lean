import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneQuadraticRows

variable {K : Type*} [CommRing K]

/-- The exact homogeneous signal from the two genuine marked reads at
the fourth regular reverse row. No diagonal or clock difference is
inverted. -/
theorem clear_adjacent_reads
    {u k n h e f d cv p q z v s ip iip ell rho tap : K}
    (huk : u*k = n*h) (he : e*h = u*ell*k) (hf : f*h = u*rho*k)
    (hcv : cv = d*u) (hz : q*z = p)
    (htap : tap = ell*k-ip+d*(s-k))
    (hmarked : (z-v)*tap = iip-rho*k) :
    (p-v*q)*((e*h-ip*u)*u+cv*(s*u-n*h))
      -q*(iip*u-f*h)*u = 0 := by
  rw [← huk, he, hf, hcv, ← hz]
  linear_combination q*u^2*hmarked - q*u^2*(z-v)*htap

/-- Coordinates for the second root of the true quadratic matched
profile; its live quadratic coefficient is paid by the literal
first-middle diagonal argument. -/
theorem second_root_coordinates
    {z x p q a1 lead : K}
    (hz : q*z = p) (hs : a1 = -lead*(z+x)) :
    q*lead*x = -q*a1-p*lead := by
  rw [← hz, hs]
  ring

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneQuadraticRows

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneQuadraticRows
#print axioms clear_adjacent_reads
#print axioms second_root_coordinates
