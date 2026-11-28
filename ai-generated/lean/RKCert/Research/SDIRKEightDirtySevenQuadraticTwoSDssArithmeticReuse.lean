import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSDssArithmeticReuse

variable {K : Type*} [CommRing K]

theorem affine_rank_zero_difference (s p q a : K) :
    (1+2*a*q)*p*(p-s) - (1+2*a*p)*q*(q-s) =
      (p-q)*(p+q-s+2*a*p*q) := by
  ring1

theorem component_scaled_singleton_fit (z l A C R S h₄ : K)
    (hA : A=R*C+h₄*S) (hl : l=h₄*z) :
    z*A-l*S=R*z*C := by
  rw [hA,hl]
  ring1

theorem scaled_overlap_quartic (mu z L f C B beta kap R : K)
    (hL : L-f*C=B*f*(f-R)) (hB : mu*B=beta*kap) :
    mu*(z*L-f*(z*C)) = z*beta*kap*f*(f-R) := by
  calc
    _ = z*mu*(L-f*C) := by ring1
    _ = z*(mu*B)*f*(f-R) := by rw [hL]; ring1
    _ = _ := by rw [hB]; ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSDssArithmeticReuse
