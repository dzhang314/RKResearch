module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EqualInvisibleReceipts

/-- For equal invisible residuals at a common physical clock, an
undetected strict residual feed cancels every scalar moment of the pair. -/
theorem equalTagMoment {R : Type*} [CommRing R]
    (g x a b h : R) (j : ℕ) (hh : h = g*(a+b)) :
    g*(a*x^j+b*x^j)=h*x^j := by
  rw [hh]
  ring

/-- Signed two-node Hankel pivots and the two monic reconstruction
numerators. Neither weight positivity nor ordering is needed. -/
theorem signedTwoSiteReconstruction {R : Type*} [CommRing R]
    (a b x y : R) :
    let m := fun j : ℕ => a*x^j+b*y^j
    m 0*m 2-(m 1)^2=a*b*(x-y)^2 ∧
      m 1*m 3-(m 2)^2=a*b*(x-y)^2*(x*y) ∧
      m 1*m 2-m 0*m 3= -(a*b*(x-y)^2*(x+y)) := by
  dsimp
  constructor
  · ring
  constructor <;> ring

/-- Three pegs leaving at most two ordinary sites force the Hankel
determinant to vanish, even when the two residual weights are signed. -/
theorem signedTwoSiteHankel {R : Type*} [CommRing R]
    (a b x y : R) :
    let m := fun j : ℕ => a*x^j+b*y^j
    m 0*m 2*m 4+2*m 1*m 2*m 3-m 0*(m 3)^2-(m 1)^2*m 4-(m 2)^3=0 := by
  dsimp
  ring

#print axioms equalTagMoment
#print axioms signedTwoSiteReconstruction
#print axioms signedTwoSiteHankel

end RKCert.ReviewedNative.SDIRK8EqualInvisibleReceipts
