module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveRearGaussReads

/-- Anchor the actual affine reverse multiplier at its Gaussian
zero without dividing by the corresponding cubic amplitude. -/
theorem affineRootCross {R : Type*} [CommRing R]
    (scale x c r k h₁ h₂ : R)
    (hx : h₁=scale*(x-r)) (hc : h₂=scale*k*(c-r)) :
    (x-r)*h₂=k*(c-r)*h₁ := by
  linear_combination (x-r)*hc-k*(c-r)*hx

/-- The two physical rear star contact placements share the same
checked scalar model after swapping the two nonterminal pegs. -/
theorem starContactSwap {R : Type*} [CommRing R]
    (u h₀ h₁ h₂ : R) :
    (2-(2-u))*h₂-(2-u)*h₁+(1+2*(2-u)-(2-u)^2)*(2*(2-u)-2)*h₀ =
      -((2-u)*h₁-u*h₂+(1+2*u-u^2)*(2*u-2)*h₀) := by
  ring

#print axioms affineRootCross
#print axioms starContactSwap

end RKCert.ReviewedNative.SDIRK8EightActiveRearGaussReads
