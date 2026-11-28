module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveSharedGaussProjection

/-- The polynomial norm of a linear read on the two roots of a monic
quadratic. It expresses the exact homogeneous early elimination
without assuming a generic diagonal specialization. -/
theorem quadraticPairNorm {R : Type*} [CommRing R]
    (a b c d x y : R) (hs : x+y = -c) (hp : x*y=d) :
    (a+b*x)*(a+b*y)=a^2-c*a*b+d*b^2 := by
  linear_combination a*b*hs+b^2*hp

/-- A literal quadratic and a linear remainder at the same actual
clock imply the cleared elimination, even at a lowered leading
coefficient. No coefficient in either read is inverted. -/
theorem quadraticLinearContact {R : Type*} [CommRing R]
    (a b c u v x : R)
    (h₁ : a+b*x+c*x^2=0) (h₂ : u+v*x=0) :
    c*u^2-b*u*v+a*v^2=0 := by
  linear_combination v^2*h₁+(c*u-c*v*x-b*v)*h₂

/-- After removing the exact Gaussian atom and masking six genuine
nonhole pegs, the one remaining clock gives the scaled linear factor
without a signed mass division. -/
theorem singletonNodalMask {R : Type*} [CommRing R]
    (m₀ m₁ ξ X : R) (h : m₁=m₀*ξ) :
    m₀*(X-ξ)=m₀*X-m₁ := by
  linear_combination h

#print axioms quadraticPairNorm
#print axioms quadraticLinearContact
#print axioms singletonNodalMask

end RKCert.ReviewedNative.SDIRK8EightActiveSharedGaussProjection
