import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Supporting arithmetic for the all-paid exactly-five one-off-clock exclusion. -/
namespace RKResearch.Certified.SDIRKEightFiveZeroOneOffClock

theorem fifth_clock_moment_elimination {R : Type*} [CommRing R] {a m₀ m₁ m₂ : R}
    (h₁ : m₁=a*m₀) (h₂ : m₂=a*m₁) : m₀*m₂-m₁^2=0 := by
  rw [h₂,h₁]
  ring

theorem fifth_clock_pinned_when_nonzero {F : Type*} [Field F] {a m₀ m₁ : F}
    (h₀ : m₀ ≠ 0) (h₁ : m₁=a*m₀) : a=m₁/m₀ := by
  exact (eq_div_iff h₀).2 h₁.symm

theorem literal_projection_numerators :
    (130321 : Nat) = 19^4 ∧ (8303 : Nat) = 19^2*23 ∧
    (529 : Nat) = 23^2 ∧ (5202961 : Nat) = 2281^2 := by
  decide +kernel

end RKResearch.Certified.SDIRKEightFiveZeroOneOffClock
