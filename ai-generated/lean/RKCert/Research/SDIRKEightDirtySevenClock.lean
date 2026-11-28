import Mathlib.Tactic.Ring.Basic

/-! Scalar receipts for the seven-clock all-dirty floor packet. -/
namespace RKResearch.Certified.SDIRKEightDirtySevenClock

variable {R : Type*} [CommRing R]

theorem two_copy_defect_norm (u v e f : R) (h : u*e+v*f=0) :
    u*e^2+v*f^2 = -(e*f)*(u+v) := by
  calc
    _ = (e+f)*(u*e+v*f)-(e*f)*(u+v) := by ring1
    _ = _ := by rw [h, mul_zero, zero_sub]

theorem constant_graph_opener_numerator (u : R) :
    (1+4*u-4*u^2)*(-2+u+4*u^2-u^3)+4*u^2*(3*u-2) -
      (-2+u+4*u^2-u^3) = 4*u*(u-2)*(u^3-3*u^2+1) := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenClock
