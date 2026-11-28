import Lean.Elab.Tactic.Grind

/-! Integer-cleared shifted Hilbert five arithmetic. This portable file
has no Mathlib dependency and uses kernel reduction, not native_decide. -/

namespace RKResearch.Certified.ERK10EndpointHilbertFive

def tile (a : List (List Int)) (i j : Fin 5) : Int :=
  ((a[i.val]?).getD [])[j.val]?.getD 0

def H : Fin 5 → Fin 5 → Int := tile
  [[1260, 840, 630, 504, 420],
   [840, 630, 504, 420, 360],
   [630, 504, 420, 360, 315],
   [504, 420, 360, 315, 280],
   [420, 360, 315, 280, 252]]

def invH : Fin 5 → Fin 5 → Int := tile
  [[450, -4200, 12600, -15120, 6300],
   [-4200, 44100, -141120, 176400, -75600],
   [12600, -141120, 470400, -604800, 264600],
   [-15120, 176400, -604800, 793800, -352800],
   [6300, -75600, 264600, -352800, 158760]]

def product (A B : Fin 5 → Fin 5 → Int) (i j : Fin 5) : Int :=
  A i 0*B 0 j + A i 1*B 1 j + A i 2*B 2 j + A i 3*B 3 j + A i 4*B 4 j

/-- H is 2520 times the shifted Hilbert matrix having entries 1/(i+j+2).
This form is independent of the coefficient field. -/
theorem scaledEntries :
    ∀ i j : Fin 5, ((i.val+j.val+2 : Nat):Int)*H i j=2520 := by decide

theorem inverseLeft :
    ∀ i j : Fin 5, product invH H i j=if i=j then 2520 else 0 := by decide

theorem inverseRight :
    ∀ i j : Fin 5, product H invH i j=if i=j then 2520 else 0 := by decide

end RKResearch.Certified.ERK10EndpointHilbertFive
#print axioms RKResearch.Certified.ERK10EndpointHilbertFive.scaledEntries
#print axioms RKResearch.Certified.ERK10EndpointHilbertFive.inverseLeft
#print axioms RKResearch.Certified.ERK10EndpointHilbertFive.inverseRight
