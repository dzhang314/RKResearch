import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenBothSingletonMixedShareRank

variable {K : Type*} [CommRing K]

theorem scale_line_determinant (a b c d lam : K)
    (h₁ : a+lam*b=0) (h₂ : c+lam*d=0) : a*d-c*b=0 := by
  calc
    _ = (a+lam*b)*d-(c+lam*d)*b := by ring1
    _ = 0 := by rw [h₁,h₂]; ring1

theorem quadratic_graph_secant (a b c H t : K) :
    let R : K → K := fun x => a+b*x+c*x^2
    H*(2*R t)-((H-t)*(2*R 0)+t*(2*R H))=2*c*H*t*(t-H) := by
  dsimp
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenBothSingletonMixedShareRank
