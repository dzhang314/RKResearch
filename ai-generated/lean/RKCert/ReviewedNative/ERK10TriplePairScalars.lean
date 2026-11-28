import Lean.Elab.Tactic.Grind

namespace RKResearch.Certified.ERK10TriplePairScalars
open Lean.Grind

section Ring
variable {R : Type} [CommRing R]

theorem exceptionalSquare (a b z A B : R)
    (p2 : 2*(a*A+b*B)=z^2)
    (p3 : 3*(a^2*A+b^2*B)=z^3)
    (p4 : 4*(a^3*A+b^3*B)-2*b*(a-b)*(a-2*b)*B=z^4) :
    z^2*(z-a)^2=0 := by
  calc
    _=a^2*z^2-2*a*z^3+z^4 := by clear p2 p3 p4; grind
    _=0 := by rw [←p2,←p3,←p4]; grind

def det3 (a b c d e f g h i : R) : R :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

theorem shiftedTripleDeterminant (a b alpha : R) :
    det3 (2*a) (2*b) (-(2*b*alpha-a^2))
        (3*a^2) (3*b^2) (-(3*b^2*alpha-a^3))
        (2*b*alpha-a^2) (-b^2) (b^2*alpha) =
    -2*a^2*b*(a^3-a^2*b-2*a*alpha*b+3*alpha*b^2) := by
  unfold det3
  grind

theorem zeroFirstQuotient (a b : R) (h : 2*a=3*b) :
    2*b^2-a^2=(a-b)*(a-2*b) := by
  calc
    _=(a-b)*(a-2*b)-a*(2*a-3*b) := by clear h; grind
    _=_ := by rw [h]; grind

end Ring

theorem exceptionalExit {F : Type} [Field F] (a b z A B : F) (znz : z ≠ 0)
    (p2 : 2*(a*A+b*B)=z^2)
    (p3 : 3*(a^2*A+b^2*B)=z^3)
    (p4 : 4*(a^3*A+b^3*B)-2*b*(a-b)*(a-2*b)*B=z^4) : z=a := by
  have h := exceptionalSquare a b z A B p2 p3 p4
  grind

end RKResearch.Certified.ERK10TriplePairScalars
#print axioms RKResearch.Certified.ERK10TriplePairScalars.shiftedTripleDeterminant
#print axioms RKResearch.Certified.ERK10TriplePairScalars.zeroFirstQuotient
#print axioms RKResearch.Certified.ERK10TriplePairScalars.exceptionalExit
