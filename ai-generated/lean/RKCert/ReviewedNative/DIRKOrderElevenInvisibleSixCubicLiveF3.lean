module

public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Exact contact and resultant derivative scalar gates -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicLiveF3

/-- A live alternate distinguishes the two roots, forcing
both coefficients of the affine pivot to vanish. -/
theorem two_distinct_affine_roots {K : Type*} [Field K] (r t a b : K)
    (hrt : r≠t) (hr : a*r+b=0) (ht : a*t+b=0) :
    a=0 ∧ b=0 := by
  have h : a*(r-t)=0 := by linear_combination hr-ht
  have ha := (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hrt)
  refine ⟨ha, ?_⟩
  simpa [ha] using hr

/-- If the affine coefficient pair vanishes, both the quadratic
resultant expression and its formal first-derivative expression
vanish. The primed inputs are arbitrary scalar derivative reads. -/
theorem zero_pivot_resultant_jet {K : Type*} [CommRing K]
    (a b A B c d e C D E : K) (ha : a=0) (hb : b=0) :
    c*b^2-d*a*b+e*a^2=0 ∧
    C*b^2+2*c*b*B-D*a*b-d*A*b-d*a*B+E*a^2+2*e*a*A=0 := by
  simp [ha,hb]

/-- Specializing at a simple factor root converts the zero derivative
into the remaining product condition. No field ordering is used. -/
theorem simple_factor_debit {K : Type*} [Field K]
    (p q r P Q R : K) (hp : p=0) (hP : P≠0) (hq : q≠0)
    (h : P*q*r+p*Q*r+p*q*R=0) : r=0 := by
  simp only [hp,zero_mul,add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hP hq)

end RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicLiveF3
