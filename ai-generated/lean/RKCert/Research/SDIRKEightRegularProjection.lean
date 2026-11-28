module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Scalar algebra used in the regular asymmetric geometric projection -/

namespace RKResearch.Certified.SDIRKEightRegularProjection

theorem even_and_odd {K : Type*} [Field K] {k e o : K}
    (h₂ : (2 : K) ≠ 0) (hk : k ≠ 0)
    (hf : e+k*o=0) (hr : e-k*o=0) : e=0 ∧ o=0 := by
  have he : (2 : K)*e=0 := by linear_combination hf+hr
  have ho : (2*k)*o=0 := by linear_combination hf-hr
  exact ⟨(mul_eq_zero.mp he).resolve_left h₂,
    (mul_eq_zero.mp ho).resolve_left (mul_ne_zero h₂ hk)⟩

theorem quadratic_norm {R : Type*} [CommRing R] {k x e o : R}
    (hk : k*k=x) (h : e+k*o=0) : e*e-x*o*o=0 := by
  linear_combination (e-k*o)*h+o^2*hk

end RKResearch.Certified.SDIRKEightRegularProjection
