import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticSddDssStar

variable {K : Type*} [CommRing K]

theorem cubic_axis_coefficient (y e c W₀ : K) :
    (y-e)*(y^2-2*c*y+W₀) =
      y^3-(e+2*c)*y^2+(W₀+2*c*e)*y-e*W₀ := by
  ring1

theorem affine_star_fit_numerator (d L r l J W : K) :
    d*L-2*r*l*J*(W-d) = d*(L+2*r*l*J)-2*r*l*J*W := by
  ring1

/-- The true terminal D fit is quadratic in the squared star gap
after multiplying by the paid nonzero denominators. -/
theorem terminal_star_clear (s d L r g C J R : K)
    (h : s*g=r*d) :
    d*(s^2*L-r*s*C-J*r*(r*d-s*R)) =
      s^2*(d*L-g*C-J*g*(g-R)) := by
  calc
    _ = d*s^2*L-(r*d)*s*C-J*(r*d)*(r*d-s*R) := by ring1
    _ = _ := by rw [← h]; ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticSddDssStar
