module

public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8InvisibleGaussDoubleReceipt

/-- The terminal profile and a normalized earlier reverse residual give
the denominator-free scalar cut. A pole or zero residual does not
justify division by that physical stage's profile. -/
theorem reverseProfileCross {R : Type*} [CommRing R]
    (x c g κ l hx hc px pc qx qc : R)
    (h₁ : hx=l*(x-g)) (h₂ : hc=l*κ*(c-g))
    (hd₁ : px=qx*hx) (hd₂ : pc=qc*hc) :
    (x-g)*pc*qx=κ*(c-g)*px*qc := by
  rw [hd₁,hd₂,h₁,h₂]
  ring

/-- The degree-three polynomial profile at the penultimate coordinate
has the exact artificial factor u=0. This factor is removable before
reduction, because a true strict tableau has a nonzero reflected gap. -/
theorem zeroGapProfile {R : Type*} [CommRing R]
    (x g α β χ δ : R) :
    (x-g)*(α+β*x+χ*x^2+δ*x^3) -
      (1+2*0-0^2)*(x-g)*(α+β*x+χ*x^2+δ*x^3)=0 := by ring

#print axioms reverseProfileCross
#print axioms zeroGapProfile

end RKCert.ReviewedNative.SDIRK8InvisibleGaussDoubleReceipt
