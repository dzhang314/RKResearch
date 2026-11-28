module

public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8CenteredTailMask

/-- The two actual centered star-tail pegs contribute a mask that depends
only on the squared gap, without choosing an orientation or square root. -/
theorem centeredTailMask {R : Type*} [CommRing R]
    (Y m γ v : R) :
    (Y-(m-γ*v))*(Y-(m+γ*v))=(Y-m)^2-γ^2*v^2 := by ring

#print axioms centeredTailMask

end RKCert.ReviewedNative.SDIRK8CenteredTailMask
