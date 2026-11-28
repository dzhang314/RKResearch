module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8OrdinaryArithmeticRearQuartic

/-- The remainder after synthetic deletion of the actual ordinary
penultimate at the actual twice-gap eighth. This formula is polynomial,
so the two true roots may coalesce in a residue chart. -/
theorem doubleGapSyntheticRemainder {R : Type*} [CommRing R]
    (r₀ r₁ r₂ r₃ r₄ u : R) :
    let f := fun X : R => r₀+r₁*X+r₂*X^2+r₃*X^3+r₄*X^4
    f (2*u)-f u = u*(r₁+3*r₂*u+7*r₃*u^2+15*r₄*u^3) := by
  dsimp
  ring

/-- Once both actual ordinary tail factors are deleted, a genuinely
different ordinary fifth still satisfies the remaining monic quadratic.
No reduced distinctness of the three clocks is asserted. -/
theorem actualFifthSurvivesTwoDeletions {R : Type*} [CommRing R] [NoZeroDivisors R]
    (u y Q : R) (hy₁ : y ≠ u) (hy₂ : y ≠ 2*u)
    (hf : (y-u)*(y-2*u)*Q=0) : Q=0 := by
  exact (mul_eq_zero.mp hf).resolve_left
    (mul_ne_zero (sub_ne_zero.mpr hy₁) (sub_ne_zero.mpr hy₂))

/-- The actual affine relation has a true nonzero denominator; this
does not license an unchecked denominator in finite specialization. -/
theorem actualSilentAffineDenominator {R : Type*} [CommRing R] [NoZeroDivisors R]
    (x c z k hx hc : R) (hxc : x ≠ c) (hk : k ≠ 0) (hx₀ : hx ≠ 0)
    (ha : (x-z)*hc = k*(c-z)*hx) : hc-k*hx ≠ 0 := by
  intro he
  rw [sub_eq_zero.mp he] at ha
  have h : (x-c)*(k*hx)=0 := by linear_combination ha
  exact (mul_ne_zero (sub_ne_zero.mpr hxc) (mul_ne_zero hk hx₀)) h

/-- The actual ordinary column eight keeps its own ordinary weight in
both backward reads. These cleared identities solve for the two
strict tail taps at columns eight only where the denominators are units. -/
theorem ordinaryEighthBackwardTwoReads {R : Type*} [CommRing R]
    (x u b₉ b₁₀ a₉ a₁₀ B BY : R)
    (h₀ : b₉*a₉+b₁₀*a₁₀=B)
    (h₁ : (x-u)*(b₉*a₉)+x*(b₁₀*a₁₀)=BY) :
    u*(b₉*a₉)=x*B-BY ∧ u*(b₁₀*a₁₀)=u*B-x*B+BY := by
  constructor
  · linear_combination x*h₀-h₁
  · linear_combination (u-x)*h₀+h₁

#print axioms doubleGapSyntheticRemainder
#print axioms actualFifthSurvivesTwoDeletions
#print axioms actualSilentAffineDenominator
#print axioms ordinaryEighthBackwardTwoReads

end RKCert.ReviewedNative.SDIRK8OrdinaryArithmeticRearQuartic
