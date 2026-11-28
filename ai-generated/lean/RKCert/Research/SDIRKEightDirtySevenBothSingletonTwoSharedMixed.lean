import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenBothSingletonTwoSharedMixed

variable {K : Type*} [CommRing K]

theorem products_cancel (L₁ L₂ B f₁ f₂ r lam : K)
    (h₁ : L₁ = -B*f₁*lam*r) (h₂ : L₂ = -B*f₂*lam*r) :
    L₁*f₂-L₂*f₁=0 := by
  rw [h₁,h₂]
  ring1

theorem scaled_vieta_sum (A B f r lam beta : K)
    (hA : A = -B*(f+lam*r)) (hbeta : beta = B*lam) :
    lam*A = -beta*(f+lam*r) := by
  rw [hA,hbeta]
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenBothSingletonTwoSharedMixed
