module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveRank

/-- At the actual zero fifth the forward taps to the three earlier
literal clocks can be read by quadratic interpolation, without a
Vandermonde inverse in the polynomial projection. -/
theorem quadraticReadFromThreeMoments {R : Type*} [CommRing R]
    (A B s p₀ p₁ p₂ a b d μ₀ μ₁ μ₂ : R)
    (h₀ : a+b+d=μ₀) (h₁ : a*A+b*B+d*s=μ₁)
    (h₂ : a*A^2+b*B^2+d*s^2=μ₂) :
    a*(p₀+p₁*A+p₂*A^2)+b*(p₀+p₁*B+p₂*B^2)+d*(p₀+p₁*s+p₂*s^2)
      =p₀*μ₀+p₁*μ₁+p₂*μ₂ := by
  linear_combination p₀*h₀+p₁*h₁+p₂*h₂

/-- The literal cubic gives a quadratic with the same three actual
earlier amplitudes once its leading coefficient times the three-peg
nodal is removed. This is not a condition at the prospective fifth. -/
theorem earlierCubicPaddedRead {R : Type*} [CommRing R]
    (x A B s h a b c d : R)
    (hx : x=A ∨ x=B ∨ x=s)
    (hval : h=a+b*x+c*x^2+d*x^3) :
    (a+d*A*B*s)+(b-d*(A*B+A*s+B*s))*x+(c+d*(A+B+s))*x^2=h := by
  rcases hx with hx|hx|hx
  all_goals
    rw [hx] at hval ⊢
    linear_combination -hval

/-- The canceled factors concern the physical fourth variable s only.
The actual normally weighted fifth has no formal Y=A, B or s pad
unless such an identity is separately proved. -/
theorem cancelFourthPadsInZeroFifthGate {R : Type*} [CommRing R] [NoZeroDivisors R]
    (s A B P : R) (hA : s≠A) (hB : s≠B)
    (h : (s-A)*(s-B)*P=0) : P=0 := by
  exact (mul_eq_zero.mp h).resolve_left
    (mul_ne_zero (sub_ne_zero.mpr hA) (sub_ne_zero.mpr hB))

#print axioms quadraticReadFromThreeMoments
#print axioms earlierCubicPaddedRead
#print axioms cancelFourthPadsInZeroFifthGate

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveRank
