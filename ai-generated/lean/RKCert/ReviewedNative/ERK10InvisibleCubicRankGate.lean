import Lean

/-! Pointwise kernel and support leaves for the invisible-ghost
cubic pure rank-three exit. -/
namespace RKResearch.ERK10InvisibleCubicRankGate
open Lean.Grind
set_option linter.unusedSectionVars false
variable {K : Type} [Field K] [IsCharP K 0]

theorem amplitudeOffCarrier (r u R beta : K) (off : u=0) (live : r≠0)
    (fit : r^2=beta*u+r*R) : r=R := by
  have eq : r*(r-R)=0 := by grind
  grind

theorem uniformCarrier (r u S rho : K) (root : S=0) (live : u≠0)
    (fit : u^2=rho*u+r*S) : u=rho := by
  have eq : u*(u-rho)=0 := by grind
  grind

theorem eraseCarrier (rho eta value : K) (live : rho≠0) :
    value-eta-((value-eta)/rho)*rho=0 := by grind

theorem fewerThanSix (s : Nat) (remaining : s≤13-6-2) : s<6 := by omega
theorem capCarriers (m n : Nat) (n8 : 8≤n) (limit : n+m≤11) :
    m≤3 := by omega
theorem dormantCap (m n a : Nat) (m2 : 2≤m) (n8 : 8≤n)
    (cnt : m+n+a=13) : a≤3 := by omega

end RKResearch.ERK10InvisibleCubicRankGate
#print axioms RKResearch.ERK10InvisibleCubicRankGate.amplitudeOffCarrier
#print axioms RKResearch.ERK10InvisibleCubicRankGate.uniformCarrier
#print axioms RKResearch.ERK10InvisibleCubicRankGate.eraseCarrier
#print axioms RKResearch.ERK10InvisibleCubicRankGate.fewerThanSix
#print axioms RKResearch.ERK10InvisibleCubicRankGate.capCarriers
#print axioms RKResearch.ERK10InvisibleCubicRankGate.dormantCap
