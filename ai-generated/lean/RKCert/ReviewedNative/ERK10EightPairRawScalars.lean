import Lean.Elab.Tactic.Grind

namespace RKResearch.Certified.ERK10EightPairRawScalars
open Lean.Grind

section Ring
variable {R : Type} [CommRing R]

theorem rawClosingG (a w₁ w₂ g u : R) (paid : 2*u=w₁*a^2) :
    a^2*w₂*g+2*g*u=a^2*(w₁+w₂)*g := by
  calc
    _=a^2*w₂*g+g*(2*u) := by clear paid; grind
    _=_ := by rw [paid]; grind

theorem rawClosingZ (a b w₁ w₂ h u : R) (paid : 2*u=w₁*a^2) :
    4*(a-b)*h-w₂*a^2*(a-b)^2-2*(a-b)^2*u =
    4*(a-b)*h-(w₁+w₂)*a^2*(a-b)^2 := by
  calc
    _=4*(a-b)*h-w₂*a^2*(a-b)^2-(a-b)^2*(2*u) := by clear paid; grind
    _=_ := by rw [paid]; grind

theorem sixthTargetPaid (p z w H : R)
    (eqn : (z-2*p)*(4*H)=w*z^2*(z-2*p)^2) :
    (z-2*p)*(4*H-w*z^2*(z-2*p))=0 := by
  calc
    _=(z-2*p)*(4*H)-w*z^2*(z-2*p)^2 := by clear eqn; grind
    _=0 := by rw [eqn]; grind

end Ring
section Field
variable {K : Type} [Field K]

theorem sixthTargetExit (p z w H : K) (gap : z ≠ 2*p)
    (eqn : (z-2*p)*(4*H)=w*z^2*(z-2*p)^2) :
    4*H=w*z^2*(z-2*p) := by
  have h := sixthTargetPaid p z w H eqn
  grind

theorem firstDormantRepeat (a b : K) (an : a ≠ 0)
    (three : (3:K) ≠ 0) : b*(2*a-b) ≠ 0 ∨ a+b ≠ 0 := by
  by_cases eq : b*(2*a-b)=0
  · right
    intro ab
    have p : 3*a=0 := by grind
    grind
  · exact Or.inl eq

end Field
end RKResearch.Certified.ERK10EightPairRawScalars
#print axioms RKResearch.Certified.ERK10EightPairRawScalars.rawClosingG
#print axioms RKResearch.Certified.ERK10EightPairRawScalars.rawClosingZ
#print axioms RKResearch.Certified.ERK10EightPairRawScalars.sixthTargetExit
#print axioms RKResearch.Certified.ERK10EightPairRawScalars.firstDormantRepeat
