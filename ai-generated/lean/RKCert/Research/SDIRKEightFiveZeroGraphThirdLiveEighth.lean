import Mathlib.Tactic.Ring

/-! Common graph parameter and two pure modes in the grade-five ingress. -/
namespace RKResearch.Certified.SDIRKEightFiveZeroGraphThirdLiveEighth

theorem common_graph_parameter_elimination {R : Type*} [CommRing R]
    {g₀ g₁ f₀ f₁ lam : R}
    (hg : g₀+lam*g₁=0) (hf : f₀+lam*f₁=0) : f₁*g₀-f₀*g₁=0 := by
  calc
    f₁*g₀-f₀*g₁=f₁*(g₀+lam*g₁)-g₁*(f₀+lam*f₁) := by ring
    _=0 := by simp [hg,hf]

theorem two_mode_three_read_det {R : Type*} [CommRing R]
    {u₀ u₁ u₂ v₀ v₁ v₂ d₀ d₁ d₂ c e : R}
    (h₀ : d₀=c*u₀+e*v₀)
    (h₁ : d₁=c*u₁+e*v₁)
    (h₂ : d₂=c*u₂+e*v₂) :
    (u₁*v₂-u₂*v₁)*d₀+(u₂*v₀-u₀*v₂)*d₁+(u₀*v₁-u₁*v₀)*d₂=0 := by
  rw [h₀,h₁,h₂]
  ring

theorem quadratic_orientation_norm {R : Type*} [CommRing R] {a b s V : R}
    (h : s^2=V) : (a+b*s)*(a-b*s)=a^2-V*b^2 := by
  calc
    (a+b*s)*(a-b*s) = a^2-s^2*b^2 := by ring
    _ = a^2-V*b^2 := by rw [h]

end RKResearch.Certified.SDIRKEightFiveZeroGraphThirdLiveEighth
