import Lean

/-! Small support-stability and residual gates for the dependent reverse chart. -/
namespace RKResearch.ERK10SingleGhostDependentRankGate
open Lean.Grind
set_option linter.unusedSectionVars false
variable {K : Type} [Field K] [IsCharP K 0]

theorem singleClockStability (c t r : K) (mask : r=0 ∨ c=t) : c*r=t*r := by
  rcases mask with z | h <;> grind

theorem twoClockStability (c x y s : K) (mask : s=0 ∨ c=x ∨ c=y) :
    c^2*s=(x+y)*c*s-x*y*s := by
  rcases mask with z | l | r <;> grind

theorem fifthResidual (R a d y D : K)
    (quad : 2*R+2*a+3*d=y^2)
    (cubic : 8*R+12*a+27*d=4*y^3)
    (quartic : 4*R+9*a+27*d=2*y^4+8*D) :
    2*R=y^2*(2*y-3)^2+16*D := by
  calc
    2*R=9*(2*R+2*a+3*d)-3*(8*R+12*a+27*d)+2*(4*R+9*a+27*d) := by grind
    _=9*y^2-3*(4*y^3)+2*(2*y^4+8*D) := by rw [quad,cubic,quartic]
    _=_ := by grind

theorem uniformPreviousClockForbidsFifth (R a d D : K)
    (uniform : 2*R=1)
    (quad : 2*R+2*a+3*d=1)
    (cubic : 8*R+12*a+27*d=4)
    (quartic : 4*R+9*a+27*d=2+8*D) :
    D=0 := by
  have q1 : 2*R+2*a+3*d=(1:K)^2 := by grind
  have q2 : 8*R+12*a+27*d=4*(1:K)^3 := by grind
  have q3 : 4*R+9*a+27*d=2*(1:K)^4+8*D := by grind
  have h := fifthResidual R a d 1 D q1 q2 q3
  clear q1 q2 q3 quad cubic quartic
  grind

end RKResearch.ERK10SingleGhostDependentRankGate
#print axioms RKResearch.ERK10SingleGhostDependentRankGate.singleClockStability
#print axioms RKResearch.ERK10SingleGhostDependentRankGate.twoClockStability
#print axioms RKResearch.ERK10SingleGhostDependentRankGate.fifthResidual
#print axioms RKResearch.ERK10SingleGhostDependentRankGate.uniformPreviousClockForbidsFifth
