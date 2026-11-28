import Mathlib.Tactic.Ring.Basic

/-!
Fourth reverse scalar identities for the seven distinct quadratic-zero
chart. The actual supported rows and field elimination are separate.
-/

namespace RKResearch.Certified.SDIRKEightSevenZeroFinalCubicFront

variable {R : Type*} [CommRing R]

/-- Compare two known affine pure readings with the fourth chronological
read without dividing by any individual output weight. -/
theorem affine_fourth_reverse
    {s t e α β Be Bs Bt Fe Js Jt Rs : R}
    (hs : -(Bs*Js)=α+β*s) (ht : -(Bt*Jt)=α+β*t)
    (he : Be*Fe-Bs*Rs=α+β*e) :
    (t-s)*(Be*Fe+Bs*(Js-Rs))+(e-s)*(Bt*Jt-Bs*Js)=0 := by
  calc
    _ = (t-s)*((Be*Fe-Bs*Rs)-(-(Bs*Js))) -
          (e-s)*((-(Bt*Jt))-(-(Bs*Js))) := by ring1
    _ = _ := by rw [hs,ht,he]; ring1

/-- Three times the reverse star arithmetic profile discrepancy. -/
def starF3 (y : R) : R := 2+6*y-3*y^2-y^3

/-- After the three ordinary star moments, the fourth reverse relation
loses its gap, except for a forbidden clock-collision factor. -/
theorem star_fourth_gap_factor (y δ h c : R) :
    starF3 y*(h*(1+y^2-δ^2)+(y-1)*(y^2-δ^2)*c) -
        h*(2+6*y-(3+y)*δ^2) =
      (y^2-δ^2)*(h*(starF3 y-3-y)+(y-1)*c*starF3 y) := by
  unfold starF3
  ring1

end RKResearch.Certified.SDIRKEightSevenZeroFinalCubicFront
