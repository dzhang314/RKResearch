/-! Scalar components of the scale-free ERK11 ordinary plateau equation. -/
namespace RKResearch.ERK11NeighborAffinePlateauArithmetic
open Lean.Grind

theorem pairCollapse {R : Type} [CommRing R] (p q t f : R) :
    q * ((q-f*p)^2 - p*(t-f*q)) + f*p^2*(t-f*q) =
      (q-f*p)*(q^2-p*t) := by
  grind

theorem scaleElimination {R : Type} [CommRing R] (u v r s g : R)
    (h1 : u+g*v=0) (h2 : r+g*s=0) : u*s-v*r=0 := by
  have h : (u+g*v)*s-v*(r+g*s) = u*s-v*r := by grind
  rw [← h, h1, h2]
  simp

theorem independentRightMark : (15*1-4*3 : Int) % 17 = 3 := by
  decide
end RKResearch.ERK11NeighborAffinePlateauArithmetic
#print axioms RKResearch.ERK11NeighborAffinePlateauArithmetic.pairCollapse
#print axioms RKResearch.ERK11NeighborAffinePlateauArithmetic.scaleElimination
#print axioms RKResearch.ERK11NeighborAffinePlateauArithmetic.independentRightMark
