import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticSddOneExtraSingleOverlap

variable {K : Type*} [CommRing K]

/-- The paid singleton equation in the true reverse residual scale,
with the fitted quadratic multiplied by that scale. -/
theorem scaled_rear_singleton_value
    (L A B rho lam T beta : K)
    (hv : L = (lam*rho)*(A+B*(lam*rho)))
    (ht : T = lam*A) (hb : beta = lam*B) :
    L = rho*T+lam*beta*rho^2 := by
  rw [hv,ht,hb]
  ring1

/-- Substitute the recovered scale in either paid affine singleton fit. -/
theorem affine_fit_after_scale_clear
    (p q D N lam : K) (h : p+lam*q=0) (hs : D*lam=N) :
    D*p+N*q=0 := by
  rw [← hs]
  calc
    _ = D*(p+lam*q) := by ring1
    _ = 0 := by rw [h,mul_zero]

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticSddOneExtraSingleOverlap
