import Lean.Elab.Tactic.Grind

namespace RKResearch.Certified.ERK10EightLabelTripleScalars
open Lean.Grind

section Ring
variable {R : Type} [CommRing R]

def det3 (a b c d e f g h i : R) : R :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

theorem delayedSecondCopyDeterminant (a b c : R) :
    let d := 3*b-2*c
    let num := 6*a^2*b-4*a^2*c+a*b^2-a*b*c-4*b^3+3*b^2*c
    det3 (2*a*(b-a)) (b*(3*b-2*a)) (c*(3*c-2*a))
         (a^3*d-a*num) (d*b*(2*b^2-a^2)) (d*c*(2*c^2-a^2))
         (2*a^2*b^2*(a-b)) (-a*b^3*d) (-a*c^2*d^2)
      = -6*a^2*b^3*c*d*(a-b)*(a-c)^2*(b-c) := by
  dsimp [det3]
  grind

theorem thirdCopyScalarDeterminant (a b : R) :
    (2*a^2)*(3*b*(2*b^2-a^2))-(3*a^3)*(2*b*(3*b-2*a))
       = 6*a^2*b*(b-a)*(2*b-a) := by grind

theorem halfTapSquare (a A T h : R)
    (p : 8*h = -4*a^2*A+a^2*T)
    (q : 8*h = -4*a^2*A-2*a^2*T) : 3*a^2*T=0 := by
  calc
    _ = (-4*a^2*A+a^2*T)-(-4*a^2*A-2*a^2*T) := by clear p q; grind
    _ = 0 := by rw [←p,←q]; grind
end Ring

theorem halfTapExit {F : Type} [Field F] (a A T h : F)
    (an : a ≠ 0) (three : (3:F) ≠ 0)
    (p : 8*h = -4*a^2*A+a^2*T)
    (q : 8*h = -4*a^2*A-2*a^2*T) : T=0 := by
  have hh := halfTapSquare a A T h p q
  grind

end RKResearch.Certified.ERK10EightLabelTripleScalars
#print axioms RKResearch.Certified.ERK10EightLabelTripleScalars.delayedSecondCopyDeterminant
#print axioms RKResearch.Certified.ERK10EightLabelTripleScalars.thirdCopyScalarDeterminant
#print axioms RKResearch.Certified.ERK10EightLabelTripleScalars.halfTapExit
