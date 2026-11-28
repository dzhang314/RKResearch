import Lean.Elab.Tactic.Omega

namespace RKResearch.Certified.Graded.OrderTwelveFifteen.MidpointFourthCore

/-- Physical midpoint shifted Legendre derivative, clearing 32. -/
theorem midpointLegendreDerivative :
    (5544 : Int)-2*13860+4*12600-8*5040+16*840-32*42=0 := by
  decide +kernel

/-- The actual repeated fifth root after clearing its square. -/
theorem clearedRepeatedRoot (q u f : Int)
    (h : (2*q*f+u)*(2*q*f+u)=0) : 2*q*f+u=0 := by
  rcases Int.mul_eq_zero.mp h with hh | hh
  · exact hh
  · exact hh

#print axioms midpointLegendreDerivative
#print axioms clearedRepeatedRoot
end RKResearch.Certified.Graded.OrderTwelveFifteen.MidpointFourthCore
