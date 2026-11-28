module

public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8HoleSevenExceptionalCramerHead

/-- Remove the actual fourth quadratic relation from the scaled fourth
pivot; the result is affine in its physical clock. -/
theorem fourthPivotCompact {R : Type*} [CommRing R]
    (A B C d₀ d₁ d₂ γ q : R) (h : A+B*q+C*q^2=0) :
    C*(d₀*γ^2+d₁*γ*q+d₂*q^2) =
      C*γ^2*d₀-d₂*A-(d₂*B-γ*d₁*C)*q := by
  linear_combination d₂*h

/-- The actual fifth law transports the sixth-clock cubic-amplitude deficit
to a coefficient polynomial independent of the physical fourth clock. -/
theorem amplitudeDeficitProjection {R : Type*} [CommRing R]
    (U V N B C h γ d₁ d₂ q y : R)
    (hN : N=B+C*(q+y)) (hV : V=d₂*(q+y)+γ*d₁)
    (hfive : U*N=8*γ^2*V*h) :
    N*(8*h*γ^2*d₂-C*U)=8*h*γ^2*(d₂*B-γ*d₁*C) := by
  linear_combination 8*h*γ^2*d₂*hN-8*h*γ^2*C*hV-C*hfive

/-- The actual pair of physical clocks four/six can be assembled from the
early quadratic and one affine correction. No ratio of amplitudes or
clock gaps is taken. -/
theorem compactActualHead {R : Type*} [CommRing R]
    (A B C L T X q w : R)
    (hq : A+B*q+C*q^2=0) (hw : L*(B+C*(q+w))+T=0) :
    L*C*(X-q)*(X-w)= L*(A+B*X+C*X^2)+T*(X-q) := by
  linear_combination -L*hq-(X-q)*hw

end RKCert.ReviewedNative.SDIRK8HoleSevenExceptionalCramerHead
