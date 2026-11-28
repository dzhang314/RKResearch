import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenBothSingletonSSSStar

variable {K : Type*}

theorem star_quadratic_coefficients [Field K] (a b u : K)
    (htwo : (2 : K) ≠ 0) (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hu2 : u ≠ 2)
    (hu : 1 + a*u+b*u^2 = 1+2*u-u^2)
    (hv : 1 + a*(2-u)+b*(2-u)^2 = 1+2*u-u^2) :
    a = 2 ∧ b = -1 := by
  have h₁ : 2*(u-1)*(a+2*b)=0 := by
    calc
      _ = (1+a*u+b*u^2)-(1+a*(2-u)+b*(2-u)^2) := by ring1
      _ = 0 := sub_eq_zero.mpr (hu.trans hv.symm)
  have hsum : a+2*b=0 :=
    (mul_eq_zero.mp h₁).resolve_left (mul_ne_zero htwo (sub_ne_zero.mpr hu1))
  have ha : a= -2*b := by
    calc
      a = (a+2*b)-2*b := by ring1
      _ = -2*b := by rw [hsum]; ring1
  have h₂ : u*(u-2)*(b+1)=0 := by
    calc
      _ = (1+(-2*b)*u+b*u^2) - (1+2*u-u^2) := by ring1
      _ = 0 := by rw [←ha,hu]; ring1
  have hb' : b+1=0 :=
    (mul_eq_zero.mp h₂).resolve_left (mul_ne_zero hu0 (sub_ne_zero.mpr hu2))
  have hb : b = -1 := by
    calc
      b = (b+1)-1 := by ring1
      _ = -1 := by rw [hb']; ring1
  refine ⟨?_,hb⟩
  rw [ha,hb]
  ring1

theorem same_reflected_star_axis [CommRing K] (w : K) :
    1+2*(1-w)-(1-w)^2 = 2-w^2 := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenBothSingletonSSSStar
