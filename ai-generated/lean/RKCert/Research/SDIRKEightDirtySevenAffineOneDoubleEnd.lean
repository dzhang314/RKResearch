import Mathlib.Tactic.Ring.Basic

/-! Scalar dimensionless clock-sum gates for the affine one-double-end exclusion. -/
namespace RKResearch.Certified.SDIRKEightDirtySevenAffineOneDoubleEnd

variable {R : Type*} [CommRing R]

theorem arithmetic_root_sum (e x : R) : e+x+(2*x+e)=2*e+3*x := by
  ring1

theorem star_root_sum (e x : R) : e+x+(2-4*e-x)=2-3*e := by
  ring1

theorem arithmetic_third_terminal (e x : R) (h : e=2*x+e) : 2*x=0 := by
  calc
    2*x = (2*x+e)-e := by ring1
    _ = 0 := by rw [← h, sub_self]

end RKResearch.Certified.SDIRKEightDirtySevenAffineOneDoubleEnd
