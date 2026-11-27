import Lean

/-! Cheap exact cells for the remaining (2,3,3) active chronology. -/
namespace RKResearch.ERK10TwoTripleFrontierGate
open Lean.Grind
variable {K : Type} [Field K]

def L (x : K) : K := 42*x^4-84*x^3+56*x^2-14*x+1

theorem bezoutDouble (x : K) :
    (182784*x^3-102144*x^2+11200*x-176)*L x
    +(-11424*x^3+17808*x^2-7084*x+235)*L (2*x)=59 := by
  unfold L
  grind

theorem noDouble (x : K) (h : L x=0) (hu : L (2*x)=0)
    (n59 : (59:K) ≠ 0) : False := by
  have b := bezoutDouble x
  rw [h,hu] at b
  clear h hu
  exact n59 (by grind)

theorem tripleCharge (x y z a b c : K)
    (h₁ : a*x+b*y+c*z=0) (h₂ : a*x^2+b*y^2+c*z^2=0) :
    a*x^3+b*y^3+c*z^3=(a+b+c)*x*y*z := by
  have hm : a*x^3+b*y^3+c*z^3 =
      (a+b+c)*x*y*z+(x+y+z)*(a*x^2+b*y^2+c*z^2)
        -(x*y+y*z+x*z)*(a*x+b*y+c*z) := by
    clear h₁ h₂
    grind
  rw [h₁,h₂] at hm
  clear h₁ h₂
  grind

end RKResearch.ERK10TwoTripleFrontierGate
#print axioms RKResearch.ERK10TwoTripleFrontierGate.bezoutDouble
#print axioms RKResearch.ERK10TwoTripleFrontierGate.noDouble
#print axioms RKResearch.ERK10TwoTripleFrontierGate.tripleCharge
