module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveStarMiddle

/-- First two signed coefficient equations for the actual linear cofactor
imply the first moment cut without dividing by the zeroth signed moment. -/
theorem firstSignedLinearCofactorCut {R : Type*} [CommRing R]
    (n m₀ m₁ m₂ f ν₄ : R) (h₁ : m₁-n*m₀=0) (h₂ : m₂-n*m₁=f*ν₄) :
    m₀*m₂-m₁^2-f*ν₄*m₀=0 := by
  linear_combination m₀*h₂-m₁*h₁

/-- The actual degree-one signed coefficient gives the second cut, still
without dividing by the zeroth signed moment. -/
theorem secondSignedLinearCofactorCut {R : Type*} [CommRing R]
    (n m₀ m₁ m₂ m₃ f ν₄ ν₅ e₅ H₃ H₄ : R)
    (h₁ : m₁-n*m₀=0)
    (h₃ : (e₅-f*H₄*n)*ν₄+f*H₄*ν₅-f*H₃*ν₄-H₄*(m₃-n*m₂)=0) :
    (e₅*ν₄+f*H₄*ν₅-f*H₃*ν₄)*m₀-f*H₄*ν₄*m₁-H₄*(m₀*m₃-m₁*m₂)=0 := by
  linear_combination m₀*h₃+(H₄*m₂-f*H₄*ν₄)*h₁

/-- At zero first pivot the actual coefficient equations still impose two
moment identities. The branch must not be silently discarded. -/
theorem zeroMomentPivotRetainsTwoConstraints {R : Type*} [CommRing R]
    (n m₀ m₁ m₂ f ν₄ : R) (h₀ : m₀=0)
    (h₁ : m₁-n*m₀=0) (h₂ : m₂-n*m₁=f*ν₄) :
    m₁=0 ∧ m₂=f*ν₄ := by
  have h : m₁=0 := by simpa [h₀] using h₁
  exact ⟨h, by simpa [h] using h₂⟩

#print axioms firstSignedLinearCofactorCut
#print axioms secondSignedLinearCofactorCut
#print axioms zeroMomentPivotRetainsTwoConstraints

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveStarMiddle
