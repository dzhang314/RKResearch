import Lean

/-! Scalar arithmetic for the two-ended sole-late ERK11 support reduction. -/
namespace RKResearch.ERK11SoleLateFrontGate
open Lean.Grind
variable {K : Type} [Field K] [IsCharP K 0]
set_option linter.unusedSectionVars false

def p3 (n x : K) := x*(x-n)*(x-2*n)
def p0 (n x : K) := x^2*(x-2*n)^2/4
def jp0 (n x : K) := x^5/20-n*x^4/4+n^2*x^3/3
def u4 (n x : K) := 3*n*x^4/4-2*n^2*x^3/3-x^5/5

theorem p0Expansion (n x : K) :
    p0 n x = x^4/4-n*x^3+n^2*x^2 := by
  unfold p0
  grind

theorem helmFifth (n f : K) (hn : n ≠ 0) :
    n*(-2*n^2)*((f+2*n^2)/(6*n)) = -n^2*(f+2*n^2)/3 := by grind

theorem quarticResidueAtRepeat (n : K) : u4 n (2*n) = 4*n^5/15 := by
  unfold u4
  grind

theorem primitiveAtRepeat (n : K) : jp0 n (2*n) = 4*n^5/15 := by
  unfold jp0
  grind

theorem plusPrimitiveIdentity (n z x : K) :
    jp0 n x + ((x-z)*p0 n x-jp0 n x) = (x-z)*p0 n x := by
  grind

theorem secondPrimitiveAtRepeat (n z : K) :
    (2*n-z)*p0 n (2*n)-jp0 n (2*n)= -4*n^5/15 := by
  unfold p0 jp0
  grind

/-- Two actual clean stage readings at the same clock recover the coefficient. -/
theorem coefficientAtRepeat (n w E delta : K)
    (n0 : n ≠ 0) (d0 : delta ≠ 0)
    (row4 : 4*n^5/15 + w*(-2*n^2)=0)
    (difference : w*delta + E*(-n^2*delta/3)=0) :
    E = 2*n/5 := by
  have h : w=2*n^3/15 := by
    clear d0 difference
    grind
  rw [h] at difference
  clear h row4
  grind

/-- The same row difference for a primitive whose polynomial lift cancels a donor relation. -/
theorem quarticAliasCoefficient (n eta delta : K)
    (n0 : n ≠ 0) (d0 : delta ≠ 0)
    (rowdifference : (-2*n^3/15)*delta+eta*(-n^2*delta/3)=0) :
    eta = -2*n/5 := by grind

theorem sixthResponse (n x f : K) (n0 : n ≠ 0) (nd : x ≠ 2*n)
    (h : p0 n x + (n/2)*(x-2*n)*f=0) :
    f = x^2*(2*n-x)/(2*n) := by
  have ht : (x-2*n)*(x^2*(x-2*n)+2*n*f)=0 := calc
    _ = 4*(p0 n x + (n/2)*(x-2*n)*f) := by
      clear n0 nd h
      unfold p0
      grind
    _ = 0 := by rw [h]; grind
  clear h
  have hc : x^2*(x-2*n)+2*n*f=0 := by
    clear n0
    grind
  clear ht nd
  grind

end RKResearch.ERK11SoleLateFrontGate
#print axioms RKResearch.ERK11SoleLateFrontGate.p0Expansion
#print axioms RKResearch.ERK11SoleLateFrontGate.helmFifth
#print axioms RKResearch.ERK11SoleLateFrontGate.quarticResidueAtRepeat
#print axioms RKResearch.ERK11SoleLateFrontGate.primitiveAtRepeat
#print axioms RKResearch.ERK11SoleLateFrontGate.plusPrimitiveIdentity
#print axioms RKResearch.ERK11SoleLateFrontGate.secondPrimitiveAtRepeat
#print axioms RKResearch.ERK11SoleLateFrontGate.coefficientAtRepeat
#print axioms RKResearch.ERK11SoleLateFrontGate.quarticAliasCoefficient
#print axioms RKResearch.ERK11SoleLateFrontGate.sixthResponse
