import Lean

/-! Two-stage weighted scalar/response and variance identities. -/
namespace RKResearch.ERK11SixPairSiteGate
open Lean.Grind
variable {K : Type} [Field K] [IsCharP K 0]
set_option linter.unusedSectionVars false

theorem poolIdentities (a b u v : K) (h : a*u+b*v=0) :
    (a+b)*u*v= -(a*u^2+b*v^2) ∧
    a*u^3+b*v^3=(u+v)*(a*u^2+b*v^2) ∧
    a*u^2+b*v^2=b*v*(v-u) := by
  constructor
  · grind
  constructor <;> grind

theorem weightedSlope (a b u v p s : K) (h : a*u+b*v=0) :
    a*u*(p+u*s)+b*v*(p+v*s)=(a*u^2+b*v^2)*s := by grind

theorem weightedProduct (a b u v p q s t : K) (h : a*u+b*v=0) :
    a*(p+u*s)*(q+u*t)+b*(p+v*s)*(q+v*t) =
            (a+b)*p*q+(a*u^2+b*v^2)*s*t := by grind

theorem preimageError (a b u v s t : K) (b0 : b ≠ 0) (h : a*u+b*v=0) :
    ((a*u^2+b*v^2)*s*t)/b=v*(v-u)*s*t := by
  have he : a*u^2+b*v^2=b*v*(v-u) := (poolIdentities a b u v h).2.2
  rw [he]
  clear h he
  grind

theorem plateauConstant (u v p : K) (u0 : u ≠ 0) (uv : u ≠ v)
    (h : p*(v-u)=v/u-1) :
    -p*u = -1 := by
  have hh : (v-u)*(p*u-1)=0 := by grind
  clear h
  grind

end RKResearch.ERK11SixPairSiteGate
#print axioms RKResearch.ERK11SixPairSiteGate.poolIdentities
#print axioms RKResearch.ERK11SixPairSiteGate.weightedSlope
#print axioms RKResearch.ERK11SixPairSiteGate.weightedProduct
#print axioms RKResearch.ERK11SixPairSiteGate.preimageError
#print axioms RKResearch.ERK11SixPairSiteGate.plateauConstant
