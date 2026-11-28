import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenBothSingletonBothTwoSShared

variable {K : Type*} [CommRing K]

theorem consistent_scale_minor (a b c d lam : K)
    (ha : a+lam*b=0) (hc : c+lam*d=0) : a*d-c*b=0 := by
  calc
    _ = (a+lam*b)*d-(c+lam*d)*b := by ring1
    _ = 0 := by rw [ha,hc]; ring1

theorem proportional_remainders (v₀ v₁ w₀ w₁ theta : K)
    (h₀ : v₀=theta*w₀) (h₁ : v₁=theta*w₁) :
    v₀*w₁-v₁*w₀=0 := by
  rw [h₀,h₁]
  ring1

theorem fourth_gate_cleared (L A B g c n : K)
    (hL : L=g*(A+B*g)) (hc : c*g=n) :
    c^2*L-A*n*c-B*n^2=0 := by
  rw [hL,←hc]
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenBothSingletonBothTwoSShared
