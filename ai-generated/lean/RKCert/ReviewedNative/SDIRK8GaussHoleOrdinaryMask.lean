module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8GaussHoleOrdinaryMask

/-- With a known signed transported atom and only one unknown
ordinary clock, subtracting that atom gives the appropriate
rank-one moment test. No division by the atom is involved. -/
theorem rankOneAfterKnownAtom {R : Type*} [CommRing R]
    (r y ν w m₀ m₁ m₂ : R)
    (h₀ : m₀=ν+w) (h₁ : m₁=ν*r+w*y)
    (h₂ : m₂=ν*r^2+w*y^2) :
    (m₀-ν)*(m₂-ν*r^2)=(m₁-ν*r)^2 := by
  rw [h₀,h₁,h₂]
  ring

#print axioms rankOneAfterKnownAtom

end RKCert.ReviewedNative.SDIRK8GaussHoleOrdinaryMask
