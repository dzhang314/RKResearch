import Mathlib.Tactic.Ring.Basic

/-! Scalar receipts for the constant graph exclusion at the seven-clock all-dirty floor. -/
namespace RKResearch.Certified.SDIRKEightDirtySevenConstant

variable {R : Type*} [CommRing R]

theorem trace_reweight_numerator (r b a ell : R) :
    r^2*a*(a+b*r)+r^2*b*ell-ell^2 =
      -(ell-r*(a+b*r))*(ell+r*a) := by
  ring1

theorem swapped_endpoint_numerator (x y c : R) :
    (c-y)*(2-x)-(c-x)*(2-y)=(c-2)*(y-x) := by
  ring1

theorem equal_singleton_arithmetic_numerator (u : R) :
    (1+4*u-4*u^2)*(-2+u+4*u^2-u^3)+4*u^2*(3*u-2) -
      (1+2*u-u^2)*(-2+u+4*u^2-u^3) =
        u*(u-2)*(3*u-2)*(u^2-2*u-1) := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenConstant
