import Lean

namespace RKResearch.ERK10InvisibleOneClockMovingGate
open Lean.Grind
set_option linter.unusedSectionVars false
variable {K : Type} [Field K] [IsCharP K 0]

theorem fourthMomentTerm (a u b r value : K)
    (fit : a*u=r^2-value*r) :
    a*(b*u^2*r)=b*u*r^3-value*(b*u*r^2) := by
  calc
    _=(b*u*r)*(a*u) := by clear fit; grind
    _=_ := by rw [fit]; grind

theorem twoAmplitudes (r val : K) (fit : r^2=val*r) :
    r=0 ∨ r=val := by
  have h : r*(r-val)=0 := by grind
  grind

theorem tapKilled (a u : K) (live : u ≠ 0) (read0 : a*u=0) :
    a=0 := by grind

theorem affineTwoZeros (a b x y : K) (apart : x ≠ y)
    (first : a+b*x=0) (second : a+b*y=0) :
    ∀ z, a+b*z=0 := by
  have h : b*(x-y)=0 := by grind
  have b0 : b=0 := by grind
  intro z
  grind

theorem correctedClockRead (theta u rho eta value : K)
    (rh : rho ≠ 0) (same : u=rho) :
    theta*(value-eta)-((value-eta)/rho)*(theta*u)=0 ∧
    (1-theta)*(value-eta)-((value-eta)/rho)*((1-theta)*u)=0 := by
  rw [same]
  constructor <;> grind

end RKResearch.ERK10InvisibleOneClockMovingGate
#print axioms RKResearch.ERK10InvisibleOneClockMovingGate.fourthMomentTerm
#print axioms RKResearch.ERK10InvisibleOneClockMovingGate.twoAmplitudes
#print axioms RKResearch.ERK10InvisibleOneClockMovingGate.tapKilled
#print axioms RKResearch.ERK10InvisibleOneClockMovingGate.affineTwoZeros
#print axioms RKResearch.ERK10InvisibleOneClockMovingGate.correctedClockRead
