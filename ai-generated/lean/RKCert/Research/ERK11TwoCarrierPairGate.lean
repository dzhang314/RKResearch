import Lean

/-! Arithmetic for the two-ended paired-response exclusion. -/
namespace RKResearch.ERK11TwoCarrierPairGate
open Lean.Grind
variable {K : Type} [Field K] [IsCharP K 0]
set_option linter.unusedSectionVars false

def h (a b : K) := 2*(1-a)^2*(a+b-1)+(2-a)^2*(a+2*b-2)
def q (a b : K) := (a*b)^3-4*(1-a)^2*(1-b)^2*(a+b-1)^2
def fdiag (a : K) := 7*a^3-24*a^2+28*a-10
def qdiag (a : K) := a^6-4*(1-a)^4*(2*a-1)^2
def poff (t : K) := -3*t^2+12*t-8
def foff (t : K) := 9*t^3-36*t^2+34*t-10
def qoff (t : K) := (poff t)^3-4*(1-t+poff t)^2*(t-1)^2
def fcoll (a : K) := (3*a-4)*(a^2-2*a+2)
def qcoll (a : K) := 5*a^3+10*a^2+4*a-8

theorem halfDifference (a b : K) :
    h a b-h b a=(a-b)*(3*(a+b)^2+a*b-12*(a+b)+8) := by
  unfold h
  grind

theorem halfSum (a b : K) :
    h a b+h b a=3*(a+b)^3-5*(a+b)*(a*b)-12*(a+b)^2+28*(a+b)-20 := by
  unfold h
  grind

theorem symmetricCharge (a b : K) :
    q a b=(a*b)^3-4*(1-(a+b)+a*b)^2*(a+b-1)^2 := by
  unfold q
  grind

theorem diagonalSubstitution (a : K) :
    h a a=fdiag a ∧ q a a=qdiag a := by
  unfold h q fdiag qdiag
  constructor <;> grind

theorem collidedSubstitution (a : K) :
    8*h (1-a/2) a=qcoll a ∧ 8*q a (1-a/2)= -a^3*fcoll a := by
  unfold h q qcoll fcoll
  constructor <;> grind

theorem offDiagonalSubstitution (t : K) :
    3*t^3-5*t*poff t-12*t^2+28*t-20=2*foff t := by
  unfold poff foff
  grind

theorem diagonalBezout (a : K) :
    (827685*a^5-3880290*a^4+6539326*a^3-5470546*a^2+2188332*a-341588)*fdiag a+
       (386253*a^2-1075082*a+848358)*qdiag a=22448 := by
  unfold fdiag qdiag
  grind

theorem offDiagonalBezout (t : K) :
    (403641*t^5-3897177*t^4+14543678*t^3-26068972*t^2+22382434*t-7486340)*foff t+
       (57663*t^2-183303*t+105248)*qoff t=347816 := by
  unfold foff qoff poff
  grind

theorem collidedBezout (a : K) :
    (-1585*a^2-4490*a-4548)*fcoll a+
       (951*a^2-2378*a+2182)*qcoll a=18928 := by
  unfold fcoll qcoll
  grind

end RKResearch.ERK11TwoCarrierPairGate
#print axioms RKResearch.ERK11TwoCarrierPairGate.halfDifference
#print axioms RKResearch.ERK11TwoCarrierPairGate.halfSum
#print axioms RKResearch.ERK11TwoCarrierPairGate.symmetricCharge
#print axioms RKResearch.ERK11TwoCarrierPairGate.diagonalSubstitution
#print axioms RKResearch.ERK11TwoCarrierPairGate.collidedSubstitution
#print axioms RKResearch.ERK11TwoCarrierPairGate.offDiagonalSubstitution
#print axioms RKResearch.ERK11TwoCarrierPairGate.diagonalBezout
#print axioms RKResearch.ERK11TwoCarrierPairGate.offDiagonalBezout
#print axioms RKResearch.ERK11TwoCarrierPairGate.collidedBezout
