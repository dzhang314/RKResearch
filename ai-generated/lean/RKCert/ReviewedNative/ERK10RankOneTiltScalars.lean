import Lean.Elab.Tactic.Grind

namespace RKResearch.Certified.ERK10RankOneTiltScalars
open Lean.Grind

section Ring
variable {R : Type} [CommRing R]

/-- Four times the primitive of X (X-h) (X-h/2). -/
theorem twoFunctionalProbe (h z : R) :
    z^4-2*h*z^3+h^2*z^2=z^2*(z-h)^2 := by grind

/-- The first two nonconstant moments distinguish J_h from E_h. -/
theorem firstSiteCannotBeProportional (h t : R)
    (lin : 2*t*h=h^2) (quad : 3*t*h^2=h^3) : h^3=0 := by
  calc
    h^3 = 3*h*h^2-2*h^3 := by clear lin quad; grind
    _=3*h*(2*t*h)-2*(3*t*h^2) := by rw [lin,quad]
    _=0 := by clear lin quad; grind

def JP60 (u v z : R) : R := 15*z^4+20*u*z^3+30*v*z^2
def JXP60 (u v z : R) : R := 12*z^5+15*u*z^4+20*v*z^3
def JJP60 (u v z : R) : R := 3*z^5+5*u*z^4+10*v*z^3

theorem integrationCommutator (u v z : R) :
    JXP60 u v z = z*JP60 u v z-JJP60 u v z := by
  unfold JXP60 JP60 JJP60
  grind

theorem rankOneSameDonorExit (h z a b c : R)
    (constant : b=h*a) (doublePrimitive : c=0) (ibp : b=z*a-c) :
    (z-h)*a=0 := by
  calc
    _=z*a-h*a := by clear constant doublePrimitive ibp; grind
    _=c := by rw [← constant,ibp]; clear constant doublePrimitive ibp; grind
    _=0 := doublePrimitive

end Ring
end RKResearch.Certified.ERK10RankOneTiltScalars

#print axioms RKResearch.Certified.ERK10RankOneTiltScalars.twoFunctionalProbe
#print axioms RKResearch.Certified.ERK10RankOneTiltScalars.firstSiteCannotBeProportional
#print axioms RKResearch.Certified.ERK10RankOneTiltScalars.integrationCommutator
#print axioms RKResearch.Certified.ERK10RankOneTiltScalars.rankOneSameDonorExit
