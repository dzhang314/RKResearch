import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackRepeatCap

/-- Identical two affine paired reads of the original fourth debut
and its putative repeat. No pivot or fit coefficient is inverted. -/
theorem duplicate_fourth_clears
    {K : Type*} [Field K] {p a k0 k1 L I J W : K}
    (hp : p≠0) (hk : k0≠k1)
    (h0 : p*(k0*L-I)=a*(J-k0*W))
    (h1 : p*(k1*L-I)=a*(J-k1*W)) :
    L*J-I*W=0 := by
  have h : p*(k0-k1)*(L*J-I*W)=0 := by
    linear_combination (J-k1*W)*h0-(J-k0*W)*h1
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hp (sub_ne_zero.mpr hk))

theorem second_repeat_live
    {K : Type*} [Field K] {a d r s E : K}
    (ha : a≠0) (hr : s≠r) (hE : E≠0)
    (h : (1+a)*d*E=a*(s-r)*E) :
    d≠0 := by
  intro hd
  have hp := mul_ne_zero (mul_ne_zero ha (sub_ne_zero.mpr hr)) hE
  exact hp (by simpa [hd] using h.symm)

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackRepeatCap

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackRepeatCap
#print axioms duplicate_fourth_clears
#print axioms second_repeat_live
