/-! Division-free ring steps for the ten-label, eleven-active flat-pair exit. -/
namespace RKResearch.ERK11TenLabelFlatPairContactGate
open Lean.Grind
variable {R : Type} [CommRing R]

theorem halfCalibrationContact
    (a d h Kh Ka Rh Rprime : R)
    (hModel : Rh=(h-a)*(h-d)*Kh)
    (hPrime : Rprime=(a-d)*Ka)
    (hHalf : 4*Kh+Ka=0) :
    4*(a-d)*Rh+(h-a)*(h-d)*Rprime=0 := by
  rw [hModel,hPrime]
  calc
    4*(a-d)*((h-a)*(h-d)*Kh)+(h-a)*(h-d)*((a-d)*Ka) =
      (a-d)*(h-a)*(h-d)*(4*Kh+Ka) := by grind
    _ = 0 := by rw [hHalf]; grind

/-- Mixed derivative contact evaluated after factoring an omitted root.
There is no cancellation, including when the scalar u or a-u is zero. -/
theorem omittedRootContact
    (a u gA gZero leftA leftZero j₀ j₁ : R)
    (hA : gA=(a-u)*leftA)
    (h0 : gZero=(-u)*leftZero)
    (hContact : j₀*leftA-j₁*leftZero=0) :
    j₀*gA*u+j₁*gZero*(a-u)=0 := by
  rw [hA,h0]
  calc
    j₀*((a-u)*leftA)*u+j₁*((-u)*leftZero)*(a-u) =
      u*(a-u)*(j₀*leftA-j₁*leftZero) := by grind
    _ = 0 := by rw [hContact]; grind

end RKResearch.ERK11TenLabelFlatPairContactGate
#print axioms RKResearch.ERK11TenLabelFlatPairContactGate.halfCalibrationContact
#print axioms RKResearch.ERK11TenLabelFlatPairContactGate.omittedRootContact
