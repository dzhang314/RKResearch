import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticOneSingletonStar

variable {K : Type*} [CommRing K]

/-- The known front and paired star residuals fix the quadratic graph. -/
theorem star_graph [IsDomain K] (u a b : K) (h₂ : (2 : K) ≠ 0)
    (hu₀ : u ≠ 0) (hu₁ : u ≠ 1) (hu₂ : u ≠ 2)
    (hf : 1+a*u+b*u^2 = 1+2*u-u^2)
    (hg : 1+a*(2-u)+b*(2-u)^2 = 1+2*u-u^2) :
    a = 2 ∧ b = -1 := by
  have ht : 2 - 2*u ≠ 0 := by
    intro hz
    have hm : 2 * (1 - u) = 0 := by
      calc
        _ = 2 - 2*u := by ring1
        _ = 0 := hz
    exact hu₁ ((sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left h₂)).symm)
  have hh : (2-2*u)*(a+2*b) = 0 := by
    calc
      _ = (1+a*(2-u)+b*(2-u)^2) - (1+a*u+b*u^2) := by ring1
      _ = 0 := by rw [hg, hf, sub_self]
  have ha : a = -2*b := by
    calc
      a = (a+2*b)-2*b := by ring1
      _ = -2*b := by rw [(mul_eq_zero.mp hh).resolve_left ht]; ring1
  have hp : u*(u-2)*(b+1) = 0 := by
    calc
      _ = (1+(-2*b)*u+b*u^2) - (1+2*u-u^2) := by ring1
      _ = 0 := by rw [← ha, hf, sub_self]
  have hb : b = -1 := by
    calc
      b = (b+1)-1 := by ring1
      _ = -1 := by
        rw [(mul_eq_zero.mp hp).resolve_left (mul_ne_zero hu₀ (sub_ne_zero.mpr hu₂))]
        ring1
  refine ⟨?_, hb⟩
  rw [ha, hb]
  ring1

theorem singleton_nodal_remainder (y s : K) :
    y*(y-s) = (y^2-2*y-1) + (1+(2-s)*y) := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticOneSingletonStar
