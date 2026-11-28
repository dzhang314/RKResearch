module

public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ConstantQuarticTail

def quartic {R : Type*} [CommRing R] (a b c d e x : R) : R :=
  a + b*x + c*x^2 + d*x^3 + e*x^4

/-- The symmetric star-tail cross equation for a quartic profile
has just a quadratic gap after three forced distinct-clock factors. -/
theorem starQuarticFactor {R : Type*} [CommRing R]
    (a b c d e x γ u : R) :
    (2-u)*quartic a b c d e (x-γ*u) - u*quartic a b c d e (x-γ*(2-u)) +
      (1+2*u-u^2)*(2*u-2)*quartic a b c d e x =
    u*(u-1)*(u-2)*(-2*quartic a b c d e x -
      γ^2*(2*c+6*d*x+12*e*x^2) + 4*(d+4*e*x)*γ^3 -
      2*e*γ^4*((u-1)^2+3)) := by
  unfold quartic
  ring

#print axioms starQuarticFactor

end RKCert.ReviewedNative.SDIRK8ConstantQuarticTail
