import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenBothSingletonBothTwoSDisjointRank

variable {K : Type*} [CommRing K]

theorem recovered_reverse_singleton (H s t f : K)
    (h : 2*H*f*t=(H-s)*(t-s)) :
    (H-s-2*H*f)*t=s*(H-s) := by
  calc
    (H-s-2*H*f)*t = s*(H-s)+((H-s)*(t-s)-2*H*f*t) := by ring1
    _ = s*(H-s) := by rw [h]; ring1

theorem paid_cubic_coefficients (m₀ m₁ m₂ m₃ l₀ l₁ r₁ r₂ : K)
    (h₀ : l₀=2*m₀) (h₁ : 2*m₁=2*l₀*r₁+l₁)
    (h₂ : m₂=l₀*r₂+l₁*r₁) (h₃ : m₃=l₁*r₂) :
    m₂-2*m₀*r₂-(2*m₁-4*m₀*r₁)*r₁=0 ∧
    m₃-(2*m₁-4*m₀*r₁)*r₂=0 := by
  constructor
  · rw [h₂,h₁,h₀]
    ring1
  · rw [h₃,h₁,h₀]
    ring1

end RKResearch.Certified.SDIRKEightDirtySevenBothSingletonBothTwoSDisjointRank
