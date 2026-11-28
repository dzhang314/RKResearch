/-! Portable scalar steps for the exact raw affine-mask split. -/
namespace RKResearch.ERK11LeftAffineMaskGate
open Lean.Grind

theorem rawAffineLoss {R : Type} [CommRing R] (g₀ g₁ t : R)
    (h : g₀+t*g₁=0) (hs : g₁=0) : g₀=0 := by
  rw [hs] at h
  grind

theorem splitRawPair {K : Type} [Field K] (Γ e₀ e₁ : K)
    (h₀ : Γ*e₀=0) (h₁ : Γ*e₁=0) :
    Γ=0 ∨ (e₀=0 ∧ e₁=0) := by
  by_cases h : Γ=0
  · exact Or.inl h
  · right
    grind

theorem forcedPhysicalAlias {K : Type} [Field K] (x a xN xD : K)
    (h : xN=x*xD) (hc : xN-a*xD=0) (hd : xD≠0) :
    x=a := by
  rw [h] at hc
  have ha : (x-a)*xD=0 := by calc
    (x-a)*xD = x*xD-a*xD := by grind
    _ = 0 := hc
  grind

end RKResearch.ERK11LeftAffineMaskGate
#print axioms RKResearch.ERK11LeftAffineMaskGate.rawAffineLoss
#print axioms RKResearch.ERK11LeftAffineMaskGate.splitRawPair
#print axioms RKResearch.ERK11LeftAffineMaskGate.forcedPhysicalAlias
