module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveArithmeticArithmeticFourth

/-- The true penultimate read at actual z = γ*s has a nonzero affine
coefficient. The homogeneous projection itself does not need its inverse. -/
theorem actualFourthArithmeticSlope {R : Type*} [CommRing R] [NoZeroDivisors R]
    (γ u x c s k Hc Hx G₀ G₁ : R)
    (hγ : γ≠0) (hu : u≠0) (hk : k≠0) (hHx : Hx≠0)
    (hc : c=x-γ*u)
    (h₀ : u*G₀=x*Hc-k*c*Hx) (h₁ : u*G₁=γ*(k*Hx-Hc))
    (hG : G₀+s*G₁=0) :
    G₁≠0 := by
  intro hB
  have hA : G₀=0 := by simpa [hB] using hG
  have hP : γ*(k*Hx-Hc)=0 := by
    linear_combination -h₁+u*hB
  have hp := (mul_eq_zero.mp hP).resolve_left hγ
  rw [hc] at h₀
  have hBad : γ*u*k*Hx=0 := by
    linear_combination -h₀+u*hA+x*hp
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hγ hu) hk) hHx) hBad

#print axioms actualFourthArithmeticSlope

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveArithmeticArithmeticFourth
