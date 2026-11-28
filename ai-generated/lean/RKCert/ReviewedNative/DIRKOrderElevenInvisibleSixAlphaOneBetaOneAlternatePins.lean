import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneBetaOneAlternatePins

variable {K : Type*} [CommRing K]

/-- Division by the known root is homogenized in the old clock.
No degree or leading-coefficient hypothesis is used. -/
theorem synthetic_divided_second_root [IsDomain K]
    {q p z x a b c d : K}
    (hq : q ≠ 0) (hpx : p=q*z) (hdist : x ≠ z)
    (hz : a+b*z+c*z^2+d*z^3=0)
    (hx : a+b*x+c*x^2+d*x^3=0) :
    (q^2*b+p*q*c+p^2*d) + (q^2*c+p*q*d)*x+q^2*d*x^2=0 := by
  have hg : q^3*a+p*q^2*b+p^2*q*c+p^3*d = 0 := by
    rw [hpx]
    linear_combination q^3 * hz
  have hh : (q*x-p) *
      ((q^2*b+p*q*c+p^2*d) + (q^2*c+p*q*d)*x+q^2*d*x^2) = 0 := by
    linear_combination q^3*hx-hg
  apply (mul_eq_zero.mp hh).resolve_left
  rw [hpx, ← mul_sub]
  exact mul_ne_zero hq (sub_ne_zero.mpr hdist)

/-- The clock-pin resultant stays necessary even if both affine columns
vanish, and is not obtained by inverting the denominator. -/
theorem marked_quadratic_pin {d0 d1 d2 g0 g1 x : K}
    (hx : d0+d1*x+d2*x^2=0) (hg : g0=x*g1) :
    d0*g1^2+d1*g0*g1+d2*g0^2=0 := by
  rw [hg]
  linear_combination g1^2 * hx

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneBetaOneAlternatePins

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneBetaOneAlternatePins
#print axioms synthetic_divided_second_root
#print axioms marked_quadratic_pin
