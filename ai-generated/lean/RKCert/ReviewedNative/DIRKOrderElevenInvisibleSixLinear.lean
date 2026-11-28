module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharP.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Undivided grade-seven and reverse ghost gates for a linear cubic profile.
The signed thirteen-stage chronology and finite clock algebra run separately;
these portably checked identities do not assert an unrestricted DIRK bound. -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixLinear

section Ring
variable {K : Type*} [CommRing K]

/-- The order-seven forward ghost hull contact at the root of the
linear cubic carrier. The terminal-head slope may be zero. -/
theorem pole_contact (f h l u q r v s m : K)
    (hz : u=0) (hg : f+u*q-h*l = -(42*m*r))
    (hh : s=r+u*v) : f-h*l+42*m*s=0 := by
  rw [hz, zero_mul, add_zero] at hg
  rw [hz, zero_mul, add_zero] at hh
  linear_combination hg+42*m*hh

/-- At the first unweighted row, the two paid primitives see
exactly the one missing diagonal tap, and its marked version.
No assumption is made on the clock or the diagonal. -/
theorem first_ghost_marks (z d n₀ n₁ v₀ v₁ e₀ e₁ r₀ r₁ : K)
    (hn₀ : v₀=n₀-d) (hn₁ : v₁=n₁-z*d)
    (he₀ : v₀+e₀=0) (he₁ : v₁+e₁=0)
    (hr₀ : r₀=n₀+e₀) (hr₁ : r₁=n₁+e₁) :
    d=r₀ ∧ r₁-z*r₀=0 := by
  constructor
  · linear_combination hn₀-he₀-hr₀
  · linear_combination hr₁+he₁-hn₁-z*(hr₀+he₀-hn₀)

/-- One forward late ghost: clear the contact denominator instead
of imposing that its reflected clock be nonzero. -/
theorem one_gap_location (ρ ξ z t e s : K)
    (hclock : z=1-ξ) (hroot : (ρ-ξ)*t = -(42*e*s)) :
    z*t=(1-ρ)*t-42*e*s := by
  linear_combination hroot+t*hclock

/-- Use the cleared linear location in a quadratic read. In
particular no quadratic leading coefficient is inverted. -/
theorem homogeneous_quadratic_mark (a b c n t z : K)
    (hclock : n=z*t) (hmark : a*z^2+b*z+c=0) :
    a*n^2+b*n*t+c*t^2=0 := by
  rw [hclock]
  linear_combination t^2*hmark

/-- A fixed reciprocal pole factor can be used even at a
formal contact: its two marked numerators have a common root
without normalizing by any ghost clock. -/
theorem contact_mark (p a b c d e f : K)
    (h₀ : d=p*a) (h₁ : e=p*b) (h₂ : f=p*c) :
    (d+e*p+f*p^2)-p*(a+b*p+c*p^2)=0 := by
  rw [h₀,h₁,h₂]
  ring
end Ring

section Field
variable {K : Type*} [Field K]

/-- The two different first-gap ghosts force the affine
remainder to be proportional to the reciprocal carrier. -/
theorem two_gap_affine_gate (z w p a b l : K) (hzw : z≠w)
    (hz : a+b*z=l*(p-z)) (hw : a+b*w=l*(p-w)) :
    a+b*p=0 := by
  have ht : (b+l)*(z-w)=0 := by linear_combination hz-hw
  have hl : b+l=0 := (mul_eq_zero.mp ht).resolve_right (sub_ne_zero.mpr hzw)
  linear_combination hz+(p-z)*hl

/-- The same argument for the commutator allows its
calibrating diagonal (hence its scalar multiplier) to vanish. -/
theorem two_gap_scaled_gate (z w p a b l m : K) (hzw : z≠w)
    (hz : m*(a+b*z)=l*(p-z)) (hw : m*(a+b*w)=l*(p-w)) :
    m*(a+b*p)=0 := by
  have h := two_gap_affine_gate z w p (m*a) (m*b) l hzw
    (by linear_combination hz) (by linear_combination hw)
  linear_combination h
end Field

end RKResearch.Certified.Graded.OrderElevenInvisibleSixLinear
