import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSFrontDdd

variable {K : Type*} [CommRing K]

theorem paid_graph_value_clear (d s a r₀ rₛ M₀ Mₛ : K)
    (h₀ : M₀=a*(-d)*r₀) (hₛ : Mₛ=a*(s-d)*rₛ)
    (h : 2*r₀=1) :
    d*Mₛ+2*M₀*(s-d)*rₛ=0 := by
  rw [h₀,hₛ]
  calc
    _ = a*d*(s-d)*rₛ*(1-2*r₀) := by ring1
    _ = 0 := by rw [h,sub_self,mul_zero]

theorem paid_reverse_scaling (L A B lam rho beta T : K)
    (hv : L=(lam*rho)*(A+B*(lam*rho)))
    (hT : T=lam*A) (hb : beta=lam*B) :
    rho*T+beta*lam*rho^2=L := by
  rw [hT,hb,hv]
  ring1

theorem paid_two_singleton_minor (a₀ a₁ b₀ b₁ lam : K)
    (h₀ : a₀+lam*b₀=0) (h₁ : a₁+lam*b₁=0) :
    a₀*b₁-a₁*b₀=0 := by
  calc
    _ = (a₀+lam*b₀)*b₁-(a₁+lam*b₁)*b₀ := by ring1
    _ = 0 := by rw [h₀,h₁,zero_mul,zero_mul,sub_self]

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSFrontDdd
