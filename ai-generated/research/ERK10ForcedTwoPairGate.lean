import Lean

/-! Exact local leaves for the two repeated active clock chart. -/
namespace RKResearch.ERK10ForcedTwoPairGate
open Lean.Grind
variable {K : Type} [Field K]

theorem meanPairMoments (a b v w : K) :
    v*a^2+w*b^2=(a+b)*(v*a+w*b)-a*b*(v+w) := by grind

theorem weightedVariance (a b v w R : K)
    (mean : v*a^2+w*b^2=R*(v*a+w*b)) :
    v*a^3+w*b^3-(v*a+w*b)*R^2 =
      (v*a+w*b)*(a-R)*(R-b) := by
  have h := congrArg (fun q : K => (a+b)*q) mean
  grind

theorem clearedPairVariance (a b v w R : K)
    (mean : v*a^2+w*b^2=R*(v*a+w*b)) :
    let nu := v*a+w*b
    let omega := v+w
    let m := R*omega-nu
    let delta := v*a^3+w*b^3-nu*R^2
    delta*(nu-a*omega)=a*nu*(R-a)*m := by
  dsimp only
  have l := weightedVariance a b v w R mean
  grind

theorem pairedCrossover (p q a b : K) (sum : a+b=0) :
    -(p*a+q*b)=(q-p)*a := by grind

/-- The derivative numerator of the first primitive of X(X-t)(X-2t). -/
theorem squaredBoundaryDerivative (x t : K) :
   2*x*(x-2*t)^2+2*x^2*(x-2*t)=4*x*(x-t)*(x-2*t) := by grind

end RKResearch.ERK10ForcedTwoPairGate
#print axioms RKResearch.ERK10ForcedTwoPairGate.meanPairMoments
#print axioms RKResearch.ERK10ForcedTwoPairGate.weightedVariance
#print axioms RKResearch.ERK10ForcedTwoPairGate.clearedPairVariance
#print axioms RKResearch.ERK10ForcedTwoPairGate.pairedCrossover
#print axioms RKResearch.ERK10ForcedTwoPairGate.squaredBoundaryDerivative
