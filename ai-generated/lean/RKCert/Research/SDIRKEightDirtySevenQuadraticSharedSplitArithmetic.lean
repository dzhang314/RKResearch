import Mathlib.Tactic.Ring.Basic

/-! Scalar identities for reducing the Legendre quartic at a split quadratic. -/
namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticSharedSplitArithmetic

variable {R : Type*} [CommRing R]

theorem split_remainder_linear (z w : R) :
    105*(z^3-2*z*w)-90*z =
      5*z*(35*w^2-3)-5*z*(35*w^2+42*w+15-21*z^2) := by
  ring1

theorem split_remainder_constant (z w : R) :
    105*(w^2-z^2*w)+90*w+9 =
      -(35*w^2-3)*(5*w+3)+5*w*(35*w^2+42*w+15-21*z^2) := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticSharedSplitArithmetic
