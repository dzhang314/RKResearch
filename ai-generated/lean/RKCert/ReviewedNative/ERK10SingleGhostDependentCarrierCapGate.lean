import Lean

/-! Localizer and physical support arithmetic for rank-two dependent ERK10. -/
namespace RKResearch.ERK10SingleGhostDependentCarrierCapGate
open Lean.Grind
variable {K : Type} [Field K]

theorem quadraticLocator [DecidableEq K] (c x y z s : K)
    (support : s=0 ∨ c=x ∨ c=y ∨ c=z) :
    (c-y)*(c-z)*s=(x-y)*(x-z)*(if c=x then s else 0) := by
  by_cases hit : c=x
  · simp [hit]
  · simp [hit]
    rcases support with w | h | h | h <;> grind

theorem twoPointMass (r s a b : K) (br : a*r+b*s=0) :
    a*r^2+b*s^2=-(a+b)*r*s := by
  calc
    a*r^2+b*s^2=(r+s)*(a*r+b*s)-(a+b)*r*s := by grind
    _=_ := by rw [br]; grind

theorem earlyCarrierCap (m q n : Nat)
    (mLarge : m≥5) (nBound : n+m≤11)
    (qLower : q≥2) (group : 2*q≤n)
    (ordinary : 6≤13-m-n+q) (twoLabels : q=2 → 6≤13-m-2*q) :
    False := by
  by_cases eq : q=2
  · have bad := twoLabels eq
    omega
  · omega

theorem fourCarrierZeroPool (q n : Nat) (nBound : n≤7)
    (qLower : q≥2) (group : 2*q≤n)
    (ordinary : 6≤13-4-n+q) (twoLabels : q=2 → 6≤13-4-2*q) :
    q=3 ∧ n=6 := by
  by_cases eq : q=2
  · have bad := twoLabels eq
    omega
  · omega

end RKResearch.ERK10SingleGhostDependentCarrierCapGate
#print axioms RKResearch.ERK10SingleGhostDependentCarrierCapGate.quadraticLocator
#print axioms RKResearch.ERK10SingleGhostDependentCarrierCapGate.twoPointMass
#print axioms RKResearch.ERK10SingleGhostDependentCarrierCapGate.earlyCarrierCap
#print axioms RKResearch.ERK10SingleGhostDependentCarrierCapGate.fourCarrierZeroPool
