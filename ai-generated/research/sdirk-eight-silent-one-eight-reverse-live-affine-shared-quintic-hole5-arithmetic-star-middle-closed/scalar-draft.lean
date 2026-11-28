module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveArithmeticStarMiddle

/-- Absorb the paid scalar nodal equation into the signed Bezout polynomial
before canceling the actual nonzero mass. This polynomial identity itself
needs neither a mass inverse nor any constraints on the coefficient ring. -/
theorem paidMassFreeSignedIdentity {R : Type*} [CommRing R]
    (x r hr β H D Dr ID BI BE BL LD : R)
    (hE : (x-r)*BE=D*hr-H*Dr)
    (hB : BL=hr*BI-β*BE)
    (hL : LD=hr*ID-β*Dr) :
    hr*((x-r)*BI-β*D+H*ID)=(x-r)*BL+H*LD := by
  linear_combination -(x-r)*hB-H*hL+β*hE

#print axioms paidMassFreeSignedIdentity

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveArithmeticStarMiddle
