import Mathlib.Tactic.Ring.Basic

/-! Scalar identities for the two doubled-prefix affine clock census. -/
namespace RKResearch.Certified.SDIRKEightDirtySevenAffineTwoDoublePrefixes

variable {R : Type*} [CommRing R]

theorem ordered_pair_norm (z b x y : R) :
    (z+b*x)*(z+b*y)=z^2+b*z*(x+y)+b^2*(x*y) := by
  ring1

theorem opposite_arithmetic_pair (x y : R) (h : y-2*x=2*y-x) : x+y=0 := by
  calc
    x+y = (2*y-x)-(y-2*x) := by ring1
    _ = 0 := by rw [h, sub_self]

end RKResearch.Certified.SDIRKEightDirtySevenAffineTwoDoublePrefixes
