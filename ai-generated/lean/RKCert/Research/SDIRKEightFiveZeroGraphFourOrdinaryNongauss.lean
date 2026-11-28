import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Native nonzero-clock primitive obstruction for the graph chronology. -/
namespace RKResearch.Certified.SDIRKEightFiveZeroGraphFourOrdinaryNongauss

theorem quadratic_two_primitive_reads_force_zero {R : Type*}
    [CommRing R] [IsDomain R] {s p₀ p₁ p₂ : R}
    (hs : s ≠ 0)
    (h₀ : p₀+p₁*s+p₂*s^2=0)
    (h₁ : 6*p₀*s+3*p₁*s^2+2*p₂*s^3=0)
    (h₂ : 6*p₀*s^2+4*p₁*s^3+3*p₂*s^4=0) :
    p₀=0 ∧ p₁=0 ∧ p₂=0 := by
  have e₁ : 6*p₀+3*p₁*s+2*p₂*s^2=0 := by
    have h : s*(6*p₀+3*p₁*s+2*p₂*s^2)=0 := by linear_combination h₁
    exact (mul_eq_zero.mp h).resolve_left hs
  have e₂ : 6*p₀+4*p₁*s+3*p₂*s^2=0 := by
    have h : s^2*(6*p₀+4*p₁*s+3*p₂*s^2)=0 := by linear_combination h₂
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hs)
  have h₀' : p₀=0 := by linear_combination h₀-e₂+e₁
  have hp₂ : p₂*s^2=0 := by linear_combination 3*e₂-4*e₁+6*h₀'
  have h₂' : p₂=0 := (mul_eq_zero.mp hp₂).resolve_right (pow_ne_zero 2 hs)
  have hp₁ : p₁*s=0 := by linear_combination h₀-h₀'-s^2*h₂'
  exact ⟨h₀',(mul_eq_zero.mp hp₁).resolve_right hs,h₂'⟩

end RKResearch.Certified.SDIRKEightFiveZeroGraphFourOrdinaryNongauss
