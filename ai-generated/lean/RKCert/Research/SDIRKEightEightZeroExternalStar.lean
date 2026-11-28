import Mathlib.Tactic.Ring.Basic

/-! Gap-free scalar arithmetic for the external live-star fourth and fifth tests. -/
namespace RKResearch.Certified.SDIRKEightEightZeroExternalStar

variable {R : Type*} [CommRing R]

theorem second_moment {w n₀ n₁ n₂ : R}
    (h₀ : n₂+(w-1)*n₁-w*n₀=0)
    (h₁ : (1-w)*(n₁-n₀)=n₀) : n₂=2*n₀ := by
  apply sub_eq_zero.mp
  calc
    _ = (n₂+(w-1)*n₁-w*n₀)+((1-w)*(n₁-n₀)-n₀) := by ring1
    _ = 0 := by rw [h₀,h₁]; ring1

theorem late_mask_cleared {w n₀ n₁ n₂ u v e₀ a₀ a₁ : R}
    (hs : (1-w)*(n₁-n₀)=n₀) (hn : n₂=2*n₀)
    (h₀ : a₀+u*n₀+v*n₁=0) (h₁ : a₁+u*n₁+v*n₂=0)
    (hc : (u+v)*n₀=(w-1)*e₀) :
    (1-w)*(a₁+w*a₀+(w^2-2)*e₀)=0 := by
  rw [hn] at h₁
  have hm : (u+v)*n₀+(1-w)*e₀=0 := by
    rw [hc]
    ring1
  calc
    _ = (1-w)*((a₁+u*n₁+v*(2*n₀))+w*(a₀+u*n₀+v*n₁))
         -(u+w*v)*((1-w)*(n₁-n₀)-n₀)
         -(2-w^2)*((u+v)*n₀+(1-w)*e₀) := by ring1
    _ = 0 := by rw [h₀,h₁,hs,hm]; ring1

theorem fourth_unmultiplied_identity (x e₀ e₁ e₂ t₀ t₁ t₂ : R) :
    let n₀ := t₁-x*t₀
    let n₁ := t₂-x*t₁
    let E₀ := e₁-x*e₀
    let E₁ := e₂-x*e₁
    (n₁-n₀)*e₁+(2*n₀-n₁)*e₀+(E₁-2*E₀)*t₀+(E₀-E₁)*t₁ =
    (2*t₁-t₂)*e₀+(t₂-2*t₀)*e₁+(t₀-t₁)*e₂ := by
  dsimp
  ring1

end RKResearch.Certified.SDIRKEightEightZeroExternalStar
