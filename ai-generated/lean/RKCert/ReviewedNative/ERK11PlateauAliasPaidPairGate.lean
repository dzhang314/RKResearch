/-! Paid ordinary moment of a plateau where one of the two responses is known. -/
namespace RKResearch.ERK11PlateauAliasPaidPairGate
open Lean.Grind
variable {R : Type} [CommRing R]

theorem twoPhysicalRows
    (b c f g : R) :
    let pool := b+c
    let nu := b*f+c*g
    let mu := b*f^2+c*g^2
    let tau := b*f^3+c*g^3
    (mu-f*nu)^2-(nu-f*pool)*(tau-f*mu)=0 := by
  dsimp
  grind

/-- The checked finite-place tuple violates the denominator-free equation. -/
theorem witness29 :
    (((28 : Int)-11*2)^2-(2-11*5)*(16-11*28)) % 29 = 17 := by decide

end RKResearch.ERK11PlateauAliasPaidPairGate
#print axioms RKResearch.ERK11PlateauAliasPaidPairGate.twoPhysicalRows
#print axioms RKResearch.ERK11PlateauAliasPaidPairGate.witness29
