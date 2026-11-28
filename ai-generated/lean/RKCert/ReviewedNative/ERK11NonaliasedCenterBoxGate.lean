/-! Scalar clearing and completion identities for the discriminant box. -/
namespace RKResearch.ERK11NonaliasedCenterBoxGate
open Lean.Grind

theorem rescaleDiscriminant {R : Type} [CommRing R] (k e₀ e₁ e₂ : R) :
    (k*e₁)^2-4*(k*e₀)*(k*e₂)=k^2*(e₁^2-4*e₀*e₂) := by
  grind

theorem discriminantAtRoot {R : Type} [CommRing R] (e₀ e₁ e₂ u : R)
    (h : e₀+e₁*u+e₂*u^2=0) :
    e₁^2-4*e₀*e₂=(2*e₂*u+e₁)^2 := by
  have he : e₀ = -e₁*u-e₂*u^2 := by grind
  rw [he]
  grind

end RKResearch.ERK11NonaliasedCenterBoxGate
#print axioms RKResearch.ERK11NonaliasedCenterBoxGate.rescaleDiscriminant
#print axioms RKResearch.ERK11NonaliasedCenterBoxGate.discriminantAtRoot
