import Lean

/-! Exact pointwise and finite-support arithmetic for the late-twelve ghost. -/
namespace RKResearch.ERK10SingleGhostTwelveMarkGate
open Lean.Grind
set_option linter.unusedSectionVars false
variable {K : Type} [Field K] [IsCharP K 0]

theorem twoNonzeroAmplitudes (x y b c : K)
    (hx : x ≠ 0) (hy : y ≠ 0) (hb : b ≠ 0)
    (moment1 : b*x+c*y=0) (moment2 : b*x^2+c*y^2=0) :
    x=y ∧ b+c=0 := by
  have hf : b*x*(x-y)=0 := by
    calc
      b*x*(x-y)= (b*x^2+c*y^2)-y*(b*x+c*y) := by grind
      _=0 := by rw [moment1,moment2]; grind
  have xy : x=y := by grind
  subst y
  have hs : (b+c)*x=0 := by grind
  exact ⟨rfl,by grind⟩

theorem equalTwoLiveMasses (x y a b c : K)
    (_hx : x ≠ 0) (_hy : y ≠ 0) (ha : a ≠ 0)
    (m0 : a+b+c=0) (m1 : a*x+(b+c)*y=0) :
    x=y := by
  have hh : a*(x-y)=0 := by
    calc
      a*(x-y)= (a*x+(b+c)*y)-y*(a+b+c) := by grind
      _=0 := by rw [m0,m1]; grind
  grind

theorem cubicOnThree (x y z a b c : K)
    (m1 : a*x+b*y+c*z=0) (m2 : a*x^2+b*y^2+c*z^2=0) :
    a*x^3+b*y^3+c*z^3=x*y*z*(a+b+c) := by
  calc
    a*x^3+b*y^3+c*z^3 =
      (x+y+z)*(a*x^2+b*y^2+c*z^2)-
        (x*y+x*z+y*z)*(a*x+b*y+c*z)+x*y*z*(a+b+c) := by grind
    _=_ := by rw [m1,m2]; grind

theorem markedCubic (a rr rs ss : K)
    (pureR : rr=0) (paidProduct : a*rr+rs=0) :
    a^2*rr+2*a*rs+ss=ss := by grind

theorem markedResponse (a rr rs ss : K)
    (paidProduct : a*rr+rs=0) :
    a^2*rr+2*a*rs+ss=a*rs+ss := by
  calc
    a^2*rr+2*a*rs+ss=a*(a*rr+rs)+(a*rs+ss) := by grind
    _=_ := by rw [paidProduct]; grind

end RKResearch.ERK10SingleGhostTwelveMarkGate
#print axioms RKResearch.ERK10SingleGhostTwelveMarkGate.twoNonzeroAmplitudes
#print axioms RKResearch.ERK10SingleGhostTwelveMarkGate.equalTwoLiveMasses
#print axioms RKResearch.ERK10SingleGhostTwelveMarkGate.cubicOnThree
#print axioms RKResearch.ERK10SingleGhostTwelveMarkGate.markedCubic
#print axioms RKResearch.ERK10SingleGhostTwelveMarkGate.markedResponse
