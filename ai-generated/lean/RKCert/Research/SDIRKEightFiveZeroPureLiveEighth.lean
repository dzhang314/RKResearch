import Mathlib.Tactic.Ring

/-! Scalar moment ingresses for the pure five-live-zero exclusion. -/
namespace RKResearch.Certified.SDIRKEightFiveZeroPureLiveEighth

theorem fifth_node_moment_is_nonzero {F : Type*} [CommRing F] [IsDomain F]
    {m₀ b w : F} (hw : w ≠ 0) (hb : b ≠ 0)
    (h : m₀ = w*b) : m₀ ≠ 0 := by
  rw [h]
  exact mul_ne_zero hw hb

theorem fifth_node_moment_minors {R : Type*} [CommRing R] {x m₀ m₁ m₂ m₃ : R}
    (h₁ : m₁=x*m₀) (h₂ : m₂=x*m₁) (h₃ : m₃=x*m₂) :
    m₀*m₂-m₁^2=0 ∧ m₀*m₃-m₁*m₂=0 := by
  constructor
  · rw [h₂,h₁]
    ring
  · rw [h₃,h₁]
    ring

theorem rear_star_pair {R : Type*} [CommRing R] (T D v : R) :
    (T-(D-3+v))*(T-(D-1-v)) = (T-D+2)^2-(v-1)^2 := by ring

end RKResearch.Certified.SDIRKEightFiveZeroPureLiveEighth
