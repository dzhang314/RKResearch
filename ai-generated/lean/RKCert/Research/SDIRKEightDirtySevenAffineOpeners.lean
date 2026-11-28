import Mathlib.Tactic.Ring.Basic

/-! Scalar affine-graph receipts for the seven-clock all-dirty floor. -/
namespace RKResearch.Certified.SDIRKEightDirtySevenAffineOpeners

variable {R : Type*} [CommRing R]

theorem affine_opening_numerator (u : R) :
    (1+4*u-4*u^2)*(-2+u+4*u^2-u^3)+4*u^2*(3*u-2) -
      (1+4*u-2*u^2)*(-2+u+4*u^2-u^3) =
        2*u^2*(u-1)^2*(u-2) := by
  ring1

theorem pair_clock_divided_difference (d y z : R) :
    (5*y^3-3*d^2*y)*(35*z^4-30*d^2*z^2+3*d^4) -
      (35*y^4-30*d^2*y^2+3*d^4)*(5*z^3-3*d^2*z) =
    (y-z)*(-9*d^6+15*d^4*y^2-75*d^4*y*z+15*d^4*z^2+
      105*d^2*y^3*z-45*d^2*y^2*z^2+105*d^2*y*z^3-175*y^3*z^3) := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenAffineOpeners
