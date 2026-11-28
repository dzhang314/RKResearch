import Lean

/-! Core-only arithmetic for the first two middle evaluation rows
of the two-ended four-carrier ERK11 chart. -/
namespace RKResearch.ERK11NeighbourPencilGate
open Lean.Grind
set_option linter.unusedSectionVars false
variable {K : Type} [Field K] [IsCharP K 0]

def den (z : K) : K := z*(z-1)^2
def phase (x z : K) : K := x*(x-1)*(x-z)*(2*x-1)
def G (x : K) : K := 6*x^2-15*x+10
def D (x z : K) : K := 6*x^2*z^2 - 24*x^2*z + 20*x^2 + 3*x*z^2 + 12*x*z - 18*x - 7*z^2 + 8*z
def Jnum (x z : K) : K := x^3*G x*(z-1)^2
def i1 (x z : K) : K := 12*x^2*z^2 - 16*x^2*z + 2*x^2 - 12*x*z^3 + 6*x*z^2 + 12*x*z - 3*x + 10*z^3 - 14*z^2 + 2*z + 1
def i2 (x z : K) : K := 8*x^2*z^2 - 10*x^2*z - 8*x*z^3 + 4*x*z^2 + 7*x*z + 6*z^3 - 8*z^2 + z
def i3 (x z : K) : K := 6*x^2*z^2 - 8*x^2*z - 6*x*z^3 + 3*x*z^2 + 6*x*z + 4*z^3 - 5*z^2
def i4 (x z : K) : K := 4*x^2*z^2 - 6*x^2*z - 5*x*z^3 + 4*x*z^2 + 4*x*z + 3*z^3 - 4*z^2
def i5 (x z : K) : K := -x^2*z^3 + 4*x^2*z^2 - 5*x^2*z - 3*x*z^3 + 3*x*z^2 + 3*x*z + 2*z^3 - 3*z^2
def w1 (x z : K) : K := 36*x^3*z^2 - 48*x^3*z + 6*x^3 - 66*x^2*z^2 + 90*x^2*z - 15*x^2 + 18*x*z^2 - 29*x*z + 10*x + 7*z^2 - 8*z
def w2 (x z : K) : K := z*(x)*(24*x^2*z - 30*x^2 - 42*x*z + 51*x + 7*z - 8)
def w3 (x z : K) : K := z*(3*x^2)*(6*x*z - 8*x - 11*z + 14)
def w4 (x z : K) : K := z*(2*x^2)*(6*x*z - 9*x - 15*z + 20)
def w5 (x z : K) : K := z*(-5*x^2)*(x + 4*z - 6)
def raw1 (x z f : K) : K := den z*x^1-f*i1 x z
def raw2 (x z f : K) : K := den z*x^2-f*i2 x z
def raw3 (x z f : K) : K := den z*x^3-f*i3 x z
def raw4 (x z f : K) : K := den z*x^4-f*i4 x z
def raw5 (x z f : K) : K := den z*x^5-f*i5 x z

theorem fit1 (z : K) :
    ((1:K)/8)*i1 (1/2) z=den z*(1/2)^1 ∧
    (-(1:K)/2)*i1 1 z=den z ∧
    (z^2*(1-z))*i1 z z=den z*z^1 := by
  unfold i1 den
  constructor
  · grind
  constructor <;> grind

theorem fit2 (z : K) :
    ((1:K)/8)*i2 (1/2) z=den z*(1/2)^2 ∧
    (-(1:K)/2)*i2 1 z=den z ∧
    (z^2*(1-z))*i2 z z=den z*z^2 := by
  unfold i2 den
  constructor
  · grind
  constructor <;> grind

theorem fit3 (z : K) :
    ((1:K)/8)*i3 (1/2) z=den z*(1/2)^3 ∧
    (-(1:K)/2)*i3 1 z=den z ∧
    (z^2*(1-z))*i3 z z=den z*z^3 := by
  unfold i3 den
  constructor
  · grind
  constructor <;> grind

theorem fit4 (z : K) :
    ((1:K)/8)*i4 (1/2) z=den z*(1/2)^4 ∧
    (-(1:K)/2)*i4 1 z=den z ∧
    (z^2*(1-z))*i4 z z=den z*z^4 := by
  unfold i4 den
  constructor
  · grind
  constructor <;> grind

theorem fit5 (z : K) :
    ((1:K)/8)*i5 (1/2) z=den z*(1/2)^5 ∧
    (-(1:K)/2)*i5 1 z=den z ∧
    (z^2*(1-z))*i5 z z=den z*z^5 := by
  unfold i5 den
  constructor
  · grind
  constructor <;> grind


theorem unaryNumerator (x z f : K) :
    10*raw3 x z f-15*raw4 x z f+6*raw5 x z f =
      z*(D x z*f+Jnum x z) := by
  unfold raw3 raw4 raw5 i3 i4 i5 den D Jnum G
  grind

theorem row1 (x z f : K) (fit : D x z*f+Jnum x z=0) :
    D x z*raw1 x z f=(z-1)^2*phase x z*w1 x z := by
  calc
    _=D x z*den z*x^1-(D x z*f)*i1 x z := by
      unfold raw1
      grind
    _=D x z*den z*x^1+Jnum x z*i1 x z := by
      have f0 : D x z*f= -Jnum x z := by grind
      rw [f0]
      grind
    _=_ := by
      clear fit
      unfold D den Jnum i1 phase w1 G
      grind

theorem row2 (x z f : K) (fit : D x z*f+Jnum x z=0) :
    D x z*raw2 x z f=(z-1)^2*phase x z*w2 x z := by
  calc
    _=D x z*den z*x^2-(D x z*f)*i2 x z := by
      unfold raw2
      grind
    _=D x z*den z*x^2+Jnum x z*i2 x z := by
      have f0 : D x z*f= -Jnum x z := by grind
      rw [f0]
      grind
    _=_ := by
      clear fit
      unfold D den Jnum i2 phase w2 G
      grind

theorem row3 (x z f : K) (fit : D x z*f+Jnum x z=0) :
    D x z*raw3 x z f=(z-1)^2*phase x z*w3 x z := by
  calc
    _=D x z*den z*x^3-(D x z*f)*i3 x z := by
      unfold raw3
      grind
    _=D x z*den z*x^3+Jnum x z*i3 x z := by
      have f0 : D x z*f= -Jnum x z := by grind
      rw [f0]
      grind
    _=_ := by
      clear fit
      unfold D den Jnum i3 phase w3 G
      grind

theorem row4 (x z f : K) (fit : D x z*f+Jnum x z=0) :
    D x z*raw4 x z f=(z-1)^2*phase x z*w4 x z := by
  calc
    _=D x z*den z*x^4-(D x z*f)*i4 x z := by
      unfold raw4
      grind
    _=D x z*den z*x^4+Jnum x z*i4 x z := by
      have f0 : D x z*f= -Jnum x z := by grind
      rw [f0]
      grind
    _=_ := by
      clear fit
      unfold D den Jnum i4 phase w4 G
      grind

theorem row5 (x z f : K) (fit : D x z*f+Jnum x z=0) :
    D x z*raw5 x z f=(z-1)^2*phase x z*w5 x z := by
  calc
    _=D x z*den z*x^5-(D x z*f)*i5 x z := by
      unfold raw5
      grind
    _=D x z*den z*x^5+Jnum x z*i5 x z := by
      have f0 : D x z*f= -Jnum x z := by grind
      rw [f0]
      grind
    _=_ := by
      clear fit
      unfold D den Jnum i5 phase w5 G
      grind


theorem rankMinor (z : K) :
    (z*(7*z-8))^2*
      ((-33*z^2+42*z)*(12*z^2-18*z)
             -(18*z^2-24*z)*(-30*z^2+40*z))
    =6*z^4*(7*z-8)^2*(24*z^2-57*z+34) := by grind

theorem completeSquare (z : K) :
    24*z^2-57*z+34=24*(z-19/16)^2+5/32 := by grind

theorem primitivePositiveNumerator (theta : K) :
    8*(70*theta^4-140*theta^3+115*theta^2-45*theta+7)
     =560*(theta-1/2)^4+80*(theta-1/2)^2+1 := by grind

theorem doublePrimitivePositiveNumerator (theta : K) :
    660*theta^4-1320*theta^3+1045*theta^2-385*theta+56
     =660*(theta-1/2)^4+55*(theta-1/2)^2+1 := by grind

end RKResearch.ERK11NeighbourPencilGate
#print axioms RKResearch.ERK11NeighbourPencilGate.fit1
#print axioms RKResearch.ERK11NeighbourPencilGate.fit2
#print axioms RKResearch.ERK11NeighbourPencilGate.fit3
#print axioms RKResearch.ERK11NeighbourPencilGate.fit4
#print axioms RKResearch.ERK11NeighbourPencilGate.fit5
#print axioms RKResearch.ERK11NeighbourPencilGate.unaryNumerator
#print axioms RKResearch.ERK11NeighbourPencilGate.row1
#print axioms RKResearch.ERK11NeighbourPencilGate.row2
#print axioms RKResearch.ERK11NeighbourPencilGate.row3
#print axioms RKResearch.ERK11NeighbourPencilGate.row4
#print axioms RKResearch.ERK11NeighbourPencilGate.row5
#print axioms RKResearch.ERK11NeighbourPencilGate.rankMinor
#print axioms RKResearch.ERK11NeighbourPencilGate.completeSquare
#print axioms RKResearch.ERK11NeighbourPencilGate.primitivePositiveNumerator
#print axioms RKResearch.ERK11NeighbourPencilGate.doublePrimitivePositiveNumerator
