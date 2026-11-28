import Mathlib.Tactic.Ring.Basic

/-! Scalar consequences for exactly-eight-zero, early--rear repeats. -/

namespace RKResearch.Certified.SDIRKEightEightZeroRearEarlyOverlap

variable {R : Type*} [CommRing R]

/-- The fourth normalized diagonal read, after the Legendre correction,
forces the quadratic mask to vanish away from the three earlier roots. -/
theorem fourth_gate [IsDomain R] {x q sig j l m : R}
    (hn : sig ≠ 0)
    (hr : (x-q)*(sig-j) = l)
    (hf : (x-q)*(sig-j)-l = sig*m) : m = 0 := by
  have hz : sig*m=0 := by
    rw [hr, sub_self] at hf
    exact hf.symm
  exact (mul_eq_zero.mp hz).resolve_left hn

/-- Division-free Cramer numerators for recovering the two coefficients
of a monic quadratic from two ordinary moment equations. -/
theorem two_moment_recovery {a b c d e f u v : R}
    (h₀ : a*u+b*v+c=0) (h₁ : d*u+e*v+f=0) :
    (a*e-b*d)*u=b*f-c*e ∧ (a*e-b*d)*v=c*d-a*f := by
  constructor
  · apply sub_eq_zero.mp
    calc
      _ = e*(a*u+b*v+c)-b*(d*u+e*v+f) := by ring1
      _ = 0 := by rw [h₀,h₁, mul_zero, mul_zero, sub_self]
  · apply sub_eq_zero.mp
    calc
      _ = a*(d*u+e*v+f)-d*(a*u+b*v+c) := by ring1
      _ = 0 := by rw [h₀,h₁, mul_zero, mul_zero, sub_self]

end RKResearch.Certified.SDIRKEightEightZeroRearEarlyOverlap
