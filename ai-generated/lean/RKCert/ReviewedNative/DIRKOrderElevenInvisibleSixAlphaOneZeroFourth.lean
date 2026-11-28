import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneZeroFourth

variable {K : Type*} [CommRing K]

/-- The fourth ordinary zero-diagonal mark annihilates its sole
early-ghost tap. In particular there is no division by 1 + lambda. -/
theorem zero_tap [IsDomain K] {z v ell lam delta j j2 p rho w k tap : K}
    (hz : z≠v) (hl : ell=lam*(v-z))
    (hi : (1+lam)*j2=ell*j+delta*p)
    (hr : (1+lam)*rho=ell^2+delta*w)
    (hq : p=w*k) (ht : tap=ell*k-j)
    (hm : (z-v)*tap=j2-rho*k) :
    tap=0 := by
  have h : (1+lam)*((z-v)*tap)= -ell*tap := by
    calc
      (1+lam)*((z-v)*tap) = (1+lam)*(j2-rho*k) := by rw [hm]
      _ = (1+lam)*j2-((1+lam)*rho)*k := by ring
      _ = (ell*j+delta*p)-(ell^2+delta*w)*k := by rw [hi,hr]
      _ = -ell*tap := by
        rw [hq,ht]
        ring
  have hh : (z-v)*tap=0 := by
    linear_combination h-tap*hl
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hz)

theorem coincident_old_primitive [IsDomain K] {z v ell lam delta j j2 p rho k tap : K}
    (hδ : delta≠0) (hz : z=v) (el : ell=0) (rh : rho=0)
    (hi : (1+lam)*j2=ell*j+delta*p)
    (hm : (z-v)*tap=j2-rho*k) :
    p=0 := by
  have hj : j2=0 := by simpa [hz,rh] using hm.symm
  have hp : delta*p=0 := by simpa [hj,el] using hi.symm
  exact (mul_eq_zero.mp hp).resolve_left hδ

theorem quartic_tap_eliminant {ell k jp ip0 w : K}
    (ht : ell*k=jp) (hq : ip0=w*k) :
    ell*ip0-w*jp=0 := by
  linear_combination ell*hq+w*ht

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneZeroFourth
