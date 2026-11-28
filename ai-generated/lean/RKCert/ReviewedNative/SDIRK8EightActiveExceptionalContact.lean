module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveExceptionalContact

/-- Clearing the one-parameter tail equation gives a common contact
numerator for the actual terminal and penultimate profile values. -/
theorem projectedContact {R : Type*} [CommRing R]
    (u J c₀ c₁ x₀ x₁ f₀ f₁ : R)
    (h₀ : u*f₀=(u-2)*c₀-J*x₀) (h₁ : u*f₁=(u-2)*c₁-J*x₁) :
    u*(f₁*x₀-f₀*x₁)=(u-2)*(c₁*x₀-c₀*x₁) ∧
      u*(f₁*c₀-f₀*c₁)=J*(c₁*x₀-c₀*x₁) := by
  constructor
  · linear_combination x₀*h₁-x₁*h₀
  · linear_combination c₀*h₁-c₁*h₀

/-- The first two moments at both actual anchored clocks make their
homogeneous profile independent of the exceptional parameter. -/
theorem projectAnchored {R : Type*} [CommRing R]
    (f₀ f₁ h₀ h₁ e : R) (ha : h₀=e) (hz : h₁=0) :
    f₁*h₀-f₀*h₁=f₁*e := by
  linear_combination f₁*ha-f₀*hz

#print axioms projectedContact
#print axioms projectAnchored

end RKCert.ReviewedNative.SDIRK8EightActiveExceptionalContact
