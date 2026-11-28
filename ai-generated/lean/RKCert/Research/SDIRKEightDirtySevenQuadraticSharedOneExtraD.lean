import Mathlib.Tactic.Ring.Basic

/-! Scalar receipts for the shared-clock one-extra-D boundary chart. -/
namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticSharedOneExtraD

variable {R : Type*} [CommRing R]

theorem star_reflected_level (d : R) : 1+2*(2-d)-(2-d)^2=1+2*d-d^2 := by
  ring1

theorem even_shared_product_difference (d : R) :
    (35*d^4-30*d^2+3)-3*(1+2*d-d^2)*(1-2*d-d^2) =
      4*d^2*(8*d^2-3) := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticSharedOneExtraD
