module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Scalar receipts for the silent quadratic supported graph -/

namespace RKResearch.Certified.SDIRKEightSilentQuadratic

theorem two_site_clean {K : Type*} [Field K] {x y p q : K}
    (hne : x ≠ y) (h₀ : p+q=0) (h₁ : x*p+y*q=0) :
    p=0 ∧ q=0 := by
  have h : (x-y)*p=0 := by linear_combination h₁-y*h₀
  have p0 := (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)
  exact ⟨p0,by simpa [p0] using h₀⟩

theorem homogenized_anchor {R : Type*} [CommRing R] {D N s E₃ E₂ E₁ E₀ : R}
    (h : N=D*s) (hz : E₃*s^3+E₂*s^2+E₁*s+E₀=0) :
    E₃*N^3+E₂*N^2*D+E₁*N*D^2+E₀*D^3=0 := by
  rw [h]
  linear_combination D^3*hz

theorem rear_19 :
    (2 : ZMod 19)*(1+2*5-5^2) ≠ (11^2-11+9) ∧
    (1+4*5-4*5^2+2*5 : ZMod 19) ≠ 0 ∧
    2*(1+4*5-4*5^2+2*5 : ZMod 19) ≠ 6^2-6+9 := by decide +kernel

end RKResearch.Certified.SDIRKEightSilentQuadratic
