import Lean

/-! Exact scalar arithmetic for the active plateau projection. -/
namespace RKResearch.ERK11SixPairPrimitiveGate
open Lean.Grind
variable {K : Type} [Field K] [IsCharP K 0]
set_option linter.unusedSectionVars false

def simpson (a f0 f1 f2 : K) := a*(f0+4*f1+f2)/6

theorem simpsonScalars (a : K) :
    simpson a 1 1 1=a ∧
    simpson a 0 (a/2) a=a^2/2 ∧
    simpson a 0 ((a/2)^2) (a^2)=a^3/3 ∧
    simpson a 0 ((a/2)^3) (a^3)=a^4/4 ∧
    simpson a 0 ((a/2)^4) (a^4)-a^5/5=a^5/120 := by
  unfold simpson
  constructor
  · grind
  constructor
  · grind
  constructor
  · grind
  constructor <;> grind

theorem projectedResponse (a u v : K)
    (a0 : a ≠ 0) (uv : u ≠ v) (hu : u = -a^2/2) :
    (-u/(v-u))*((a/2)*u*((v-u)/(3*a)))= -a^4/24 := by
  have h : (-u/(v-u))*((a/2)*u*((v-u)/(3*a))) = -u^2/6 := by
    clear hu
    grind
  rw [h,hu]
  clear h hu
  grind

theorem scalarDefectCancellation (a h s : K) :
    (-a^5/120)*h*s + (a/5)*s*((a^4/24)*h)=0 := by grind

end RKResearch.ERK11SixPairPrimitiveGate
#print axioms RKResearch.ERK11SixPairPrimitiveGate.simpsonScalars
#print axioms RKResearch.ERK11SixPairPrimitiveGate.projectedResponse
#print axioms RKResearch.ERK11SixPairPrimitiveGate.scalarDefectCancellation
