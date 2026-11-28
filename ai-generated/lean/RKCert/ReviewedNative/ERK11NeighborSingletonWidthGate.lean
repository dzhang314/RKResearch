/-! Local mixed support and dormant split identities for the neighboring singleton. -/
namespace RKResearch.ERK11NeighborSingletonWidthGate
open Lean.Grind

theorem paidTwoClockGap {R : Type} [CommRing R] (I₀ I₁ I₂ s z : R)
    (h : I₂-(s+z)*I₁+s*z*I₀=0) :
    (z-s)*(I₁-s*I₀)=I₂-2*s*I₁+s^2*I₀ := by
  have he : I₂=(s+z)*I₁-s*z*I₀ := by grind
  rw [he]
  grind

theorem primitiveMeter {R : Type} [CommRing R] (b p B v J α : R)
    (hJ : J=b*p*B*v) (hα : α=b*p*B^2) :
    α*v=J*B := by
  rw [hJ,hα]
  grind

end RKResearch.ERK11NeighborSingletonWidthGate
#print axioms RKResearch.ERK11NeighborSingletonWidthGate.paidTwoClockGap
#print axioms RKResearch.ERK11NeighborSingletonWidthGate.primitiveMeter
