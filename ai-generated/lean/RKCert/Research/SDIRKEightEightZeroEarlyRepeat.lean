import Mathlib.Tactic.Ring.Basic

/-! Scalar gates for the exactly-eight-zero, early-only duplicate chart.
The tableau flags and exact number-field projections are documented separately. -/

namespace RKResearch.Certified.SDIRKEightEightZeroEarlyRepeat

variable {R : Type*} [CommRing R]

/-- A monic linear last label of a moment problem forces the three
two-column minors to vanish, without any ordinary moment pivot. -/
theorem linear_tail_minors {x a b c p q r : R}
    (ha : p = x*a) (hb : q = x*b) (hc : r = x*c) :
    a*q-b*p=0 ∧ a*r-c*p=0 ∧ b*r-c*q=0 := by
  rw [ha,hb,hc]
  exact ⟨by ring1, by ring1, by ring1⟩

/-- Star gap cancellation follows from the first ordinary recovery row.
Here J is the common shifted-linear and scalar moment. -/
theorem star_cardinal_factor (d K J : R) :
    (2-d^2)*(K-J)-(K-d^2*J)=(1-d^2)*(K-2*J) := by
  ring1

/-- The monic quadratic norm gate is valid also at a split or double root. -/
theorem monic_quadratic_norm (l₀ l₁ z p q : R)
    (hz : z^2+l₁*z+l₀=0) (hs : p+q*z=0) :
    p^2-p*q*l₁+q^2*l₀=0 := by
  calc
    _ = (p+q*z)*(p-q*l₁-q*z)+q^2*(z^2+l₁*z+l₀) := by ring1
    _ = 0 := by rw [hz,hs,zero_mul,mul_zero,zero_add]

end RKResearch.Certified.SDIRKEightEightZeroEarlyRepeat
