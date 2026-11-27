module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8SevenDistinctAnchors

/-- The discrepancy at one active Gauss clock is a zero cubic
amplitude, with precisely its Gauss weight. This uses a nonzero
ordinary weight, not a positivity hypothesis. -/
theorem singleGaussHole {K : Type*} [Field K]
    (b ν h p : K) (hb : b ≠ 0) (hp : p ≠ 0) (hd : h ≠ p)
    (h₁ : b*h=(b-ν)*p) (h₂ : b*h^2=(b-ν)*p^2) :
    h=0 ∧ b=ν := by
  have hf : h*(b*(h-p))=0 := by
    linear_combination h₂-p*h₁
  have hz := (mul_eq_zero.mp hf).resolve_right (mul_ne_zero hb (sub_ne_zero.mpr hd))
  have hf' : (b-ν)*p=0 := by
    rw [hz,mul_zero] at h₁
    exact h₁.symm
  exact ⟨hz,sub_eq_zero.mp ((mul_eq_zero.mp hf').resolve_right hp)⟩

/-- A silent physical eighth gives the same reverse ratio even if
another silent stage also balances the terminal clock. The needed
input is its own actual two-tap relation, not that w₈ is the full
negative terminal weight. -/
theorem silentEighthNoSoleBalance {K : Type*} [Field K]
    (g u b₉ b₁₀ h₉ h₁₀ a₈ a₉ α β w w₈ : K)
    (hg : g ≠ 0) (hb₉ : b₉ ≠ 0) (hb₁₀ : b₁₀ ≠ 0) (hw₈ : w₈ ≠ 0)
    (hW : w=-(g*g*b₁₀))
    (hW₈ : w₈=2*g*u*b₁₀*a₈)
    (h₈read : 0=α*w₈+β*w*a₈)
    (h₉read : b₉*h₉=β*w*a₉) (h₉tap : b₁₀*a₉=b₉*g*u)
    (hterminal : b₁₀*h₁₀=α*w) :
    h₉=2*u^2*h₁₀ := by
  have ha₈ : a₈ ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hW₈
    exact hw₈ hW₈
  have hc : 2*u*α-g*β=0 := by
    have hf : (2*u*α-g*β)*(g*b₁₀*a₈)=0 := by
      linear_combination -h₈read-α*hW₈-β*a₈*hW
    exact (mul_eq_zero.mp hf).resolve_right (mul_ne_zero (mul_ne_zero hg hb₁₀) ha₈)
  have h₉' : b₁₀*h₉=β*w*g*u := by
    have hf : (b₁₀*h₉-β*w*g*u)*b₉=0 := by
      linear_combination b₁₀*h₉read+β*w*h₉tap
    exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hb₉)
  have hf : (h₉-2*u^2*h₁₀)*b₁₀=0 := by
    linear_combination h₉'-2*u^2*hterminal-w*u*hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hb₁₀)

#print axioms singleGaussHole
#print axioms silentEighthNoSoleBalance

end RKCert.ReviewedNative.SDIRK8SevenDistinctAnchors
