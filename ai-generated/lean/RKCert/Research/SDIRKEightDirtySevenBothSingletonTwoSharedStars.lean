import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenBothSingletonTwoSharedStars

variable {K : Type*} [Field K]

theorem symmetric_quadratic_linear_zero (a b c d : K)
    (htwo : (2 : K) ≠ 0) (hd : d ≠ 0)
    (h : a+b*d+c*d^2 = a+b*(-d)+c*(-d)^2) : b = 0 := by
  have e : 2*d*b=0 := by
    calc
      _ = (a+b*d+c*d^2)-(a+b*(-d)+c*(-d)^2) := by ring1
      _ = 0 := sub_eq_zero.mpr h
  exact (mul_eq_zero.mp e).resolve_left (mul_ne_zero htwo hd)

theorem symmetric_vieta_quartic (z : K) (hfour : (4 : K) ≠ 0)
    (hendpoint : z ≠ 1)
    (h : 35*z^2-120*z+48 = -37*(2-z)^2) : 18*z = 49 := by
  have e : 4*(z-1)*(18*z-49)=0 := by
    calc
      _ = (35*z^2-120*z+48)+37*(2-z)^2 := by ring1
      _ = 0 := by rw [h]; ring1
  exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left
    (mul_ne_zero hfour (sub_ne_zero.mpr hendpoint)))

end RKResearch.Certified.SDIRKEightDirtySevenBothSingletonTwoSharedStars
