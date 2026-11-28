/-! Scalar projective transition when an initial inverse-Gram slope vanishes. -/
namespace RKResearch.ERK11InitialSlopeFallbackGate
open Lean.Grind

theorem orthogonalDirection {R : Type} [CommRing R]
    (l₀ l₁ c₀ c₁ e₀ e₁ : R)
    (hp : l₀*c₀-l₁*c₁=0) :
    l₀*(c₀*e₀-c₁*e₁)=c₁*(l₁*e₀-l₀*e₁) := by
  have h : l₀*c₀=l₁*c₁ := by grind
  calc
    l₀*(c₀*e₀-c₁*e₁) = (l₀*c₀)*e₀-l₀*c₁*e₁ := by grind
    _ = c₁*(l₁*e₀-l₀*e₁) := by rw [h]; grind

theorem zeroFirstSlope {K : Type} [Field K]
    (l₀ l₁ c₀ c₁ : K) (hp : l₀*c₀-l₁*c₁=0)
    (h0 : l₀=0) (h1 : c₁≠0) :
    l₁=0 := by
  rw [h0] at hp
  grind

end RKResearch.ERK11InitialSlopeFallbackGate
#print axioms RKResearch.ERK11InitialSlopeFallbackGate.orthogonalDirection
#print axioms RKResearch.ERK11InitialSlopeFallbackGate.zeroFirstSlope
