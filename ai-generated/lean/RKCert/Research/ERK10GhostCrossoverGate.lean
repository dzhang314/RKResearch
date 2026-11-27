import Lean

/-! Exact algebraic receipts for the grade-seven invisible-ghost crossover. -/
namespace RKResearch.ERK10GhostCrossoverGate
open Lean.Grind
variable {K : Type} [Field K]

theorem bothLanes (a b q r : K)
    (paid : a*q+b*r=0) (measured : a*q ≠ 0 ∨ b*r ≠ 0) :
    a*q ≠ 0 ∧ b*r ≠ 0 := by
  rcases measured with h | h
  · exact ⟨h,by intro z; exact h (by grind)⟩
  · exact ⟨by intro z; exact h (by grind),h⟩

theorem uniformLane (rho w : K)
    (localized : rho*w=0) : rho^2*w=0 := by
  have h := congrArg (fun x : K => rho*x) localized
  grind

theorem qTwoCleanBudget (nAlpha nBeta clean : Nat)
    (a : 4≤nAlpha) (b : 4≤nBeta) (c : nAlpha+nBeta+clean=13) : clean≤5 := by
  omega

end RKResearch.ERK10GhostCrossoverGate
#print axioms RKResearch.ERK10GhostCrossoverGate.bothLanes
#print axioms RKResearch.ERK10GhostCrossoverGate.uniformLane
#print axioms RKResearch.ERK10GhostCrossoverGate.qTwoCleanBudget
