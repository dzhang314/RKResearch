import Lean.Elab.Tactic.Grind

namespace RKResearch.Certified.ERK10FirstEndpointJumpScalars
open Lean.Grind

section Ring
variable {R : Type} [CommRing R]
def det3 (a b c d e f g h i : R) : R :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

theorem firstJumpCompatibility (b z : R) :
    let d := 2*b-3
    let s := 4*d-2*d*z-2*(b-1)*z*(z-1)
    2*d * det3 4 (-z^2) 2 (6*b) (-z^3) (3-z) (8*b^2*d) (-z^4*d) s
      - 2*b*d^2 * det3 (-4) (-z^2) 2 (-6) (-z^3) (3-z) (-8*d) (-z^4*d) s
      - (z-1)*(d-2*z) *
          det3 (-4) 4 (-z^2) (-6) (6*b) (-z^3) (-8*d) (8*b^2*d) (-z^4*d)
    = 48*d*z^3*(z-b)^2*(b-1)*(z-1) := by
  dsimp [det3]
  grind

theorem twoLabelMomentFactor (z w u m₁ m₂ m₃ : R)
    (h₁ : 2*m₁=w*z^2+2*u)
    (h₂ : 3*m₂=w*z^3+(3-z)*u)
    (h₃ : 4*m₃=w*z^4+(4-2*z^2)*u)
    (cubic : m₃=3*m₂-2*m₁) :
    z*(z-2)*(w*z*(z-2)-2*u)=0 := by
  calc
    _=(w*z^4+(4-2*z^2)*u)-4*(w*z^3+(3-z)*u)+4*(w*z^2+2*u) := by
      clear h₁ h₂ h₃ cubic
      grind
    _=0 := by rw [←h₁,←h₂,←h₃,cubic]; grind
end Ring

section Field
variable {F : Type} [Field F]

theorem paidHalf (k u h : F) (un : u ≠ 0) (p : 2*h = -u) (q : h = -k*u) :
    2*k=1 := by
  have hn : (2*k-1)*u=0 := by grind
  grind

theorem twoLabelMomentExit (z w u m₁ m₂ m₃ : F) (zn : z ≠ 0) (zt : z ≠ 2)
    (h₁ : 2*m₁=w*z^2+2*u)
    (h₂ : 3*m₂=w*z^3+(3-z)*u)
    (h₃ : 4*m₃=w*z^4+(4-2*z^2)*u)
    (cubic : m₃=3*m₂-2*m₁) :
    w*z*(z-2)=2*u := by
  have h := twoLabelMomentFactor z w u m₁ m₂ m₃ h₁ h₂ h₃ cubic
  clear h₁ h₂ h₃ cubic m₁ m₂ m₃
  grind

end Field
end RKResearch.Certified.ERK10FirstEndpointJumpScalars
#print axioms RKResearch.Certified.ERK10FirstEndpointJumpScalars.firstJumpCompatibility
#print axioms RKResearch.Certified.ERK10FirstEndpointJumpScalars.paidHalf
#print axioms RKResearch.Certified.ERK10FirstEndpointJumpScalars.twoLabelMomentExit
