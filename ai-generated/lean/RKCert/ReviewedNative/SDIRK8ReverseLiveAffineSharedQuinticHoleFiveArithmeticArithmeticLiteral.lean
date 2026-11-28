module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveArithmeticArithmeticLiteral

/-- The quadratic gap factor is a polynomial identity, not a deletion of an
arithmetic rear coefficient. The literal profile remainders are arbitrary. -/
theorem arithmeticRearTrueGapFactor {R : Type*} [CommRing R]
    (γ u hx hc hd τ ρc ρd : R)
    (hC : hc=hx-γ*u*τ+u^2*ρc) (hD : hd=hx-2*γ*u*τ+u^2*ρd) :
    (-2+u+4*u^2-u^3)*hd+2*(2+3*u-12*u^2+4*u^3)*hc-
      (1+2*u-u^2)*(2+3*u-12*u^2+4*u^3)*hx =
    u^2*((4*u^3-20*u^2+30*u-12)*hx-2*γ*(3*u^2-8*u+4)*τ+
      (-2+u+4*u^2-u^3)*ρd+2*(2+3*u-12*u^2+4*u^3)*ρc) := by
  rw [hC,hD]
  ring

/-- For the actual reverse-live literal clock z, the penultimate gap factor
is exactly one power of u, with both of its clock terms kept. -/
theorem literalPenultimateTrueGapFactor {R : Type*} [CommRing R]
    (x c z γ u hx hc τ ρc : R)
    (hclock : c=x-γ*u) (hC : hc=hx-γ*u*τ+u^2*ρc) :
    (x-z)*hc-(1+2*u-u^2)*(c-z)*hx =
      u*((x-z)*(-γ*τ+u*ρc-(2-u)*hx)+(1+2*u-u^2)*γ*hx) := by
  rw [hclock,hC]
  ring

#print axioms arithmeticRearTrueGapFactor
#print axioms literalPenultimateTrueGapFactor

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveArithmeticArithmeticLiteral
