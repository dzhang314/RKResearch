import Mathlib.Tactic.Ring.Basic

/-! Scalar external finite-gap eliminations; no tableau or coefficient field assumption. -/
namespace RKResearch.Certified.SDIRKEightEightZeroExternalFinite

variable {R : Type*} [CommRing R]

theorem divided_phase_mean {n₀ n₁ n₂ p₀ p₁ p₂ p₃ v w lam : R}
    (h₀ : n₀=lam*(p₁-w*p₀)) (h₁ : n₁=lam*(p₂-w*p₁))
    (h₂ : n₂=lam*(p₃-w*p₂)) (hp : p₃=v^2*p₁) :
    n₂+w*n₁+(w^2-v^2)*n₀=-(lam*w*(w^2-v^2)*p₀) := by
  rw [h₀,h₁,h₂,hp]
  ring1

theorem collapse_phase_rows {n₀ n₁ n₂ p₀ p₁ p₂ p₃ e₀ e₁ e₂ w lam U V : R}
    (hn₀ : n₀=lam*(p₁-w*p₀)) (hn₁ : n₁=lam*(p₂-w*p₁))
    (hn₂ : n₂=lam*(p₃-w*p₂))
    (hc : e₀+lam*(U*p₀+V*p₁)=0)
    (ha : e₁-w*e₀+U*n₀+V*n₁=0)
    (hb : e₂-w*e₁+U*n₁+V*n₂=0) :
    (e₁+lam*(U*p₁+V*p₂)=0) ∧ (e₂+lam*(U*p₂+V*p₃)=0) := by
  have h₁ : e₁+lam*(U*p₁+V*p₂)=0 := by
    calc
      _ = (e₁-w*e₀+U*n₀+V*n₁)+w*(e₀+lam*(U*p₀+V*p₁)) := by
        rw [hn₀,hn₁]
        ring1
      _ = 0 := by rw [ha,hc]; ring1
  refine ⟨h₁, ?_⟩
  calc
    _ = (e₂-w*e₁+U*n₁+V*n₂)+w*(e₁+lam*(U*p₁+V*p₂)) := by
      rw [hn₁,hn₂]
      ring1
    _ = 0 := by rw [hb,h₁]; ring1

theorem fourth_unmultiplied (x e₀ e₁ e₂ t₀ t₁ t₂ p₀ p₁ p₂ : R) :
    let n₀ := t₁-x*t₀
    let n₁ := t₂-x*t₁
    let E₀ := e₁-x*e₀
    let E₁ := e₂-x*e₁
    (p₀*n₁-p₁*n₀)*e₁-(p₁*n₁-p₂*n₀)*e₀
        +(-p₂*E₀+p₁*E₁)*t₀+(p₁*E₀-p₀*E₁)*t₁ =
      (p₂*t₁-p₁*t₂)*e₀+(p₀*t₂-p₂*t₀)*e₁+(p₁*t₀-p₀*t₁)*e₂ := by
  dsimp
  ring1

end RKResearch.Certified.SDIRKEightEightZeroExternalFinite
