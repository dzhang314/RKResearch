import Lean

/-! Closed orthogonality and root split certificates for the two forced-pair exits. -/
namespace RKResearch.ERK10TwoPairFiniteExitGate
def jacobi3 : List Int := [-1,9,-21,14]
def lobatto4 : List Int := [1,-14,56,-84,42]
def eval (p : List Int) (x : Int) : Int := p.foldr (fun a v => a+x*v) 0
def beta (i : Nat) : Int := 2520/((i+2)*(i+3):Int)
def weighted (p : List Int) (i : Nat) : Int :=
  p.zipIdx.foldl (fun a (b,j) => a+b*beta (i+j)) 0

theorem cubicMoment : ∀ i : Fin 3, weighted jacobi3 i.val=0 := by decide
theorem quarticMoment : ∀ i : Fin 4, weighted lobatto4 i.val=0 := by decide

theorem splitCubic37 :
    [12,19,26].all (fun x => eval jacobi3 x%37==0) = true := by decide
theorem splitQuartic227 :
    [24,51,177,204].all (fun x => eval lobatto4 x%227==0) = true := by decide
theorem primeTrials :
    (∀ d : Fin 7, 2≤d.val → 37%d.val≠0) ∧
    (∀ d : Fin 16, 2≤d.val → 227%d.val≠0) := by decide

end RKResearch.ERK10TwoPairFiniteExitGate
#print axioms RKResearch.ERK10TwoPairFiniteExitGate.cubicMoment
#print axioms RKResearch.ERK10TwoPairFiniteExitGate.quarticMoment
#print axioms RKResearch.ERK10TwoPairFiniteExitGate.splitCubic37
#print axioms RKResearch.ERK10TwoPairFiniteExitGate.splitQuartic227
#print axioms RKResearch.ERK10TwoPairFiniteExitGate.primeTrials
