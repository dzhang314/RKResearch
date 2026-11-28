module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleEightMiddle

open scoped Matrix

/-- Two actual known ordinary pegs license a homogeneous linear
combination of the nonconstant signed coefficient rows. -/
theorem signedTwoPegDifference {R : Type*} [CommRing R]
    (a b c₀ c₁ c₂ c₃ Δ Wa Wb : R)
    (ha : c₀+c₁*a+c₂*a^2+c₃*a^3=Δ*Wa)
    (hb : c₀+c₁*b+c₂*b^2+c₃*b^3=Δ*Wb) :
    (a-b)*(c₁+(a+b)*c₂+(a^2+a*b+b^2)*c₃)=Δ*(Wa-Wb) := by
  linear_combination ha-hb

/-- The exact signed determinant has a genuine early determinant
factor after the known difference of pegs is accounted for. This
identity uses no rank pivot or specialization assumption. -/
theorem signedFrontDeterminantFactor {R : Type*} [CommRing R]
    (d Δ k l x₀ x₁ x₂ y₀ y₁ y₂ z₀ z₁ z₂ t₀ t₁ t₂ : R)
    (h₀ : d*(x₀+k*y₀+l*z₀)=Δ*t₀)
    (h₁ : d*(x₁+k*y₁+l*z₁)=Δ*t₁)
    (h₂ : d*(x₂+k*y₂+l*z₂)=Δ*t₂) :
    d*(Matrix.det !![x₀,x₁,x₂; y₀,y₁,y₂; z₀,z₁,z₂]) =
      Δ*(Matrix.det !![t₀,t₁,t₂; y₀,y₁,y₂; z₀,z₁,z₂]) := by
  simp [Matrix.det_fin_three]
  linear_combination (y₁*z₂-y₂*z₁)*h₀+(y₂*z₀-y₀*z₂)*h₁+(y₀*z₁-y₁*z₀)*h₂

#print axioms signedTwoPegDifference
#print axioms signedFrontDeterminantFactor

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleEightMiddle
