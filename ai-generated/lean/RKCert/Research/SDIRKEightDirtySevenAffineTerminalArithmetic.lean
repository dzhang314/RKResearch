import Mathlib.Tactic.Ring.Basic

/-! Scalar guard for the terminal-doubled affine arithmetic opener. -/
namespace RKResearch.Certified.SDIRKEightDirtySevenAffineTerminalArithmetic

variable {R : Type*} [CommRing R]

theorem a_one_cubic_gate (u : R) :
    (-2+u+4*u^2-u^3)-2*(u-2)*(u^3-3*u^2+1) =
      -(u-1)*(2*u^3-7*u^2+u+2) := by
  ring1

theorem unit_gap_values :
    (1+2*(1:R)-(1:R)^2)=2 ∧
      (-2+(1:R)+4*(1:R)^2-(1:R)^3) = 2*((1:R)-2)*((1:R)^3-3*(1:R)^2+1) := by
  constructor <;> ring1

end RKResearch.Certified.SDIRKEightDirtySevenAffineTerminalArithmetic
