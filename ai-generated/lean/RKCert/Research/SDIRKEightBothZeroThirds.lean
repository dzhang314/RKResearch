module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Two literal zero-third gap reads and their linear Cramer pivot -/

namespace RKResearch.Certified.SDIRKEightBothZeroThirds

theorem linear_determinant {R : Type*} [CommRing R] (s u v : R) :
    (s*(1-u)-1)*(2-v)+(s*(1-v)-1)*(2-u) =
      (4-3*(u+v)+2*u*v)*s-(4-(u+v)) := by ring

theorem first_Cramer_numerator {R : Type*} [CommRing R] (s u v : R) :
    (u*(2*s^2+2*s+1)+2*s)*(2-v)-(v*(2*s^2+2*s+1)+2*s)*(2-u) =
      2*(u-v)*(s+1)*(2*s+1) := by ring

theorem unequal_singular {K : Type*} [Field K] {s u v : K}
    (h₂ : (2 : K) ≠ 0) (hu : u ≠ v) (hs : s+1 ≠ 0)
    (h : 2*(u-v)*(s+1)*(2*s+1)=0) : 2*s+1=0 := by
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (mul_ne_zero h₂ (sub_ne_zero.mpr hu)) hs)

theorem opposite_pins {K : Type*} [Field K] {v T p₂ p₁ p₀ : K}
    (h₂ : (2 : K) ≠ 0) (hv : v ≠ 0)
    (hf : T*v^3+p₂*v^2+p₁*v+p₀=0)
    (hr : T*(-v)^3+p₂*(-v)^2+p₁*(-v)+p₀=0) :
    p₁+T*v^2=0 ∧ p₀+p₂*v^2=0 := by
  have h₁ : (2*v)*(p₁+T*v^2)=0 := by linear_combination hf-hr
  have h₀ : (2 : K)*(p₀+p₂*v^2)=0 := by linear_combination hf+hr
  exact ⟨(mul_eq_zero.mp h₁).resolve_left (mul_ne_zero h₂ hv),
    (mul_eq_zero.mp h₀).resolve_left h₂⟩

end RKResearch.Certified.SDIRKEightBothZeroThirds
