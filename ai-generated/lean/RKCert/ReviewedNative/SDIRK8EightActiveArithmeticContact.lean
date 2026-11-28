module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveArithmeticContact

/-- The arithmetic midpoint has half the affine terminal multiplier
when the physical eighth multiplier is zero. This gives the stronger
eighth Gauss-contact gate without a cleared-arithmetic pole division. -/
theorem gaussEighthMidpoint {R : Type*} [CommRing R]
    (x c d p₀ p₁ scale k hx hc : R)
    (hmid : 2*c=x+d) (hd : p₀+p₁*d=0)
    (hxread : hx=scale*(p₀+p₁*x)) (hcread : hc=scale*k*(p₀+p₁*c)) :
    2*hc=k*hx := by
  linear_combination 2*hcread-k*hxread+scale*k*p₁*hmid+scale*k*hd

/-- This knot mask is the exact affine numerator evaluated at the
arithmetic Gauss eighth; no ratio of defects is required. -/
theorem gaussEighthAffineNumerator {R : Type*} [CommRing R]
    (x c d Vx Vc : R)
    (hmid : 2*c=x+d) (hhalf : 2*Vc=Vx) :
    (d-c)*Vx+(x-d)*Vc=0 := by
  linear_combination (x-c)*hhalf+(Vc-Vx)*hmid

#print axioms gaussEighthMidpoint
#print axioms gaussEighthAffineNumerator

end RKCert.ReviewedNative.SDIRK8EightActiveArithmeticContact
