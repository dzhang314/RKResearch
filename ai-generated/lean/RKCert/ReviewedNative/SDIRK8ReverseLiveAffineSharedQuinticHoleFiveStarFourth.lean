module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveStarFourth

/-- A true literal fourth satisfies the actual quadratic front equation
and the affine centered rear read. Homogeneous elimination is valid even
if the putative affine pivot vanishes. -/
theorem actualFourthQuadraticLinearProjection {R : Type*} [CommRing R]
    (s J0 J1 J2 U0 U1 : R)
    (hJ : J0+J1*s+J2*s^2=0) (hU : U0+U1*s=0) :
    J2*U0^2-J1*U0*U1+J0*U1^2=0 := by
  linear_combination U1^2*hJ - (J1*U1+J2*(U1*s-U0))*hU

#print axioms actualFourthQuadraticLinearProjection

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveStarFourth
