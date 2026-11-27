module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8InvisibleVirtualRead

/-- A weighted mixture of two physical rows at the same clock evaluates
an affine defect read at zero if its signed defect aggregate is zero.
No assumption of positivity or of equal physical defects is needed. -/
theorem virtualAffine {K : Type*} [Field K]
    (r s h k a b : K) (hw : r+s≠0) (hh : r*h+s*k=0) :
    (r*(a+b*h)+s*(a+b*k))/(r+s)=a := by
  apply (div_eq_iff hw).2
  linear_combination b*hh

/-- Each literal padded-clock factor in the first-active comparison occurs
twice: once in the masked taps, once in the pure support correction. -/
theorem doubleMask {R : Type*} [CommRing R] (j l u v t : R) :
    j*l*(j*v)-(j*t)*(j*u)=j^2*(l*v-t*u) := by ring

#print axioms virtualAffine
#print axioms doubleMask

end RKCert.ReviewedNative.SDIRK8InvisibleVirtualRead
