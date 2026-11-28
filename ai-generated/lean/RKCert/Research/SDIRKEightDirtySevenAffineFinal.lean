import Mathlib.Tactic.Ring.Basic

/-! Scalar homogeneous late-singleton identities for the final affine chart. -/
namespace RKResearch.Certified.SDIRKEightDirtySevenAffineFinal

variable {R : Type*} [CommRing R]

theorem late_singleton_homogeneous (v d z : R) :
    2*z*(v*d-2*d)*((v*d)^3-3*(v*d)^2*d+d^3) -
        d^2*(-2*d^3+(v*d)*d^2+4*(v*d)^2*d-(v*d)^3) =
      d^4*(2*z*(v-2)*(v^3-3*v^2+1)-d*(-2+v+4*v^2-v^3)) := by
  ring1

theorem norm_on_two_choices (a b r q : R) :
    (a+b*r)*(a+b*q)=a^2+(r+q)*a*b+(r*q)*b^2 := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenAffineFinal
