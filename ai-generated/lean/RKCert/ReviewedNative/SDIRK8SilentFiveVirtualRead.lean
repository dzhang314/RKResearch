module

public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8SilentFiveVirtualRead

/-- On one physical clock, a signed silent pair whose defect moment is
zero has exactly the affine zero-defect read, even if neither physical
defect is zero. This is the division-free form used in the reverse test. -/
theorem signedSilentRead {R : Type*} [CommRing R]
    (a b w h k u v : R)
    (h₀ : a+b+w=0) (h₁ : a*h+b*k=0) :
    a*(u+v*h)+b*(u+v*k) = -w*u := by
  linear_combination u*h₀+v*h₁

#print axioms signedSilentRead

end RKCert.ReviewedNative.SDIRK8SilentFiveVirtualRead
