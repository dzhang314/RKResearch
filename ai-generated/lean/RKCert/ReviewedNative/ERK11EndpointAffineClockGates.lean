/-! Field cancellation of the two actual cleared endpoint-chart clock reads. -/
namespace RKResearch.ERK11EndpointAffineClockGates
open Lean.Grind

theorem leftActualCollision {K : Type} [Field K] (H C x a : K)
    (hH : H≠0) (hs : H*x=C) (h : C-a*H=0) :
    x=a := by
  rw [← hs] at h
  have hprod : H*(x-a)=0 := by calc
    H*(x-a) = H*x-a*H := by grind
    _ = 0 := h
  grind

theorem rightActualCollision {K : Type} [Field K] (zN zD z d : K)
    (hD : zD≠0) (hs : zN=z*zD) (h : zN-d*zD=0) :
    z=d := by
  rw [hs] at h
  have hprod : (z-d)*zD=0 := by calc
    (z-d)*zD = z*zD-d*zD := by grind
    _ = 0 := h
  grind

end RKResearch.ERK11EndpointAffineClockGates
#print axioms RKResearch.ERK11EndpointAffineClockGates.leftActualCollision
#print axioms RKResearch.ERK11EndpointAffineClockGates.rightActualCollision
