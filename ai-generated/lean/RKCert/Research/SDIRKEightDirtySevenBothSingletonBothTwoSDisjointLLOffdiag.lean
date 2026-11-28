import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenBothSingletonBothTwoSDisjointLLOffdiag

variable {K : Type*} [CommRing K]

theorem unshared_beta_row (Xp Xq Up Uq beta : K)
    (hp : Xp=beta*Up) (hq : Xq=beta*Uq) :
    Xp*Uq-Xq*Up=0 := by
  rw [hp,hq]
  ring1

theorem low_curvature_cleared (H a b M : K)
    (hM : M=(b-2)*H*(H-a)-2*H+a+b) :
    (2-a)*M-(a-b)*(H-2)=(H-a)*((2-a)*(b-2)*H+a+b-4) := by
  rw [hM]
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenBothSingletonBothTwoSDisjointLLOffdiag
