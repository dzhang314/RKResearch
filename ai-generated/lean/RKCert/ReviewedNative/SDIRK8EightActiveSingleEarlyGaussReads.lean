module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveSingleEarlyGaussReads

/-- A literal fourth evaluation clears the free profile direction
without any generic leading-coefficient assumption. -/
theorem fourthBlend {R : Type*} [CommRing R]
    (b h₀ h₁ c₀ c₁ h₄ : R) (hq : h₀+b*h₁=h₄) :
    h₁*(c₀+b*c₁)=h₁*c₀+(h₄-h₀)*c₁ := by
  linear_combination c₁*hq

/-- At an actual literal quartic root, the cubic-read coefficient is
pinned and the other literal fixes the affine intercept at its own clock. -/
theorem anchoredGaussAffine {R : Type*} [CommRing R]
    (eta a lₐ l_b m_b hₐ h_b : R)
    (hA : hₐ=eta*lₐ) (hB : h_b=eta*l_b+a*m_b) :
    lₐ*(h_b-a*m_b)=hₐ*l_b := by
  linear_combination lₐ*hB-l_b*hA

#print axioms fourthBlend
#print axioms anchoredGaussAffine

end RKCert.ReviewedNative.SDIRK8EightActiveSingleEarlyGaussReads
