module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8OrdinaryArithmeticRearGaps

/-- The three literal backward rows, after factoring ordinary weights
from their columns, have normalized columns at tail abscissae
`x-2u, x-u, x` and actual reverse ratios `rho, -k, -1`. -/
theorem normalizedSuffixDet {R : Type*} [CommRing R] (x u rho k : R) :
    ((x-u)*(-1)-x*(-k))
      - ((x-2*u)*(-1)-x*rho)
      + ((x-2*u)*(-k)-(x-u)*rho)
    = u*(rho+2*k-1) := by ring

/-- The actual arithmetic reverse ratio has only two possible nonzero
normalized gaps at which the literal backward rows lose their pivot. -/
theorem clearedArithmeticSuffixPivot {R : Type*} [CommRing R]
    (u rho h j k : R)
    (hh : h = -2+u+4*u^2-u^3)
    (hj : j = 2+3*u-12*u^2+4*u^3)
    (hk : k = 1+2*u-u^2)
    (hr : h*rho = k*j) :
    h*(u*(rho+2*k-1)) = -2*u^3*(u-1)^2*(u-2) := by
  rw [hh,hj,hk] at hr
  rw [hh,hk]
  linear_combination u*hr

#print axioms normalizedSuffixDet
#print axioms clearedArithmeticSuffixPivot

end RKCert.ReviewedNative.SDIRK8OrdinaryArithmeticRearGaps
