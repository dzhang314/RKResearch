module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8AffineLiteralAnchors

/-- A genuinely active literal and a sole transported literal provide
two actual nonzero weighted readings that pin the affine denominator. -/
theorem affinePinnedByTwoDefects {K : Type*} [Field K]
    (a b h₀ h₁ p₀ p₁ q₀ q₁ r₀ r₁ : K)
    (hd : b-a ≠ 0) (h₀n : h₀ ≠ 0) (h₁n : h₁ ≠ 0)
    (ha : h₀*(q₀+q₁*a)=p₀) (ha' : h₀*(r₀+r₁*a)=p₀)
    (hb : h₁*(q₀+q₁*b)=p₁) (hb' : h₁*(r₀+r₁*b)=p₁) :
    q₀=r₀ ∧ q₁=r₁ := by
  have e₀ : (q₀+q₁*a-(r₀+r₁*a))*h₀=0 := by linear_combination ha-ha'
  have e₁ : (q₀+q₁*b-(r₀+r₁*b))*h₁=0 := by linear_combination hb-hb'
  have f₀ := (mul_eq_zero.mp e₀).resolve_right h₀n
  have f₁ := (mul_eq_zero.mp e₁).resolve_right h₁n
  have h : (q₁-r₁)*(b-a)=0 := by linear_combination f₁-f₀
  have hq := (mul_eq_zero.mp h).resolve_right hd
  have hq' : q₀=r₀ := by linear_combination f₀-a*hq
  exact ⟨hq',sub_eq_zero.mp hq⟩

#print axioms affinePinnedByTwoDefects

end RKCert.ReviewedNative.SDIRK8AffineLiteralAnchors
