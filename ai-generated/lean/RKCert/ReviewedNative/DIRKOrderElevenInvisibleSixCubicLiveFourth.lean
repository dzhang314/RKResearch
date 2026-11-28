module

public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Undivided simultaneous fourth-clean primitives -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicLiveFourth

section Ring
variable {K : Type*} [CommRing K]

/-- The extra double primitive is retained even when the affine
slope is minus one. -/
theorem uncanceled_double_primitive (v p p₁ p₀ q d ip ip₁ ip₀ j r r₁ w t : K)
    (hp : p₁=v*p-p₀) (hi : ip₁=v*ip-j-ip₀) (hr : r₁=v*r-t-w)
    (h₀ : ip-d*(p-q)=r*q)
    (h₁ : ip₁-d*(p₁-v*q)=r₁*q)
    (hw : ip₀-d*p₀=w*q) : j=t*q := by
  rw [hp,hi,hr] at h₁
  linear_combination v*h₀-h₁-hw

/-- The two affinity coefficients locate the exact slope-minus-one profile. -/
theorem slope_minus_one (a r s c₀ c₂ : K)
    (h₀ : 4*a*s = -5*c₀) (h₁ : 12*a-15*(r-c₂)=r) :
    16*r*s=15*(c₂*s-c₀) := by
  linear_combination 3*h₀-s*h₁
end Ring

section Field
variable {K : Type*} [Field K]

/-- All three true fourth-clean reads imply a zero diagonal as long
as the genuine extra carrier coefficient is live. The multiplier
(1+ell_1) is represented by `a` and is never inverted. -/
theorem fourth_diagonal_zero (p q p₀ d ip ip₀ j r w t δ a : K)
    (hδ : δ*p₀≠0)
    (hp : ip=r*p+δ*p₀)
    (h₀ : ip-d*(p-q)=r*q)
    (hw : ip₀-d*p₀=w*q)
    (hj : j=t*q)
    (hInt : a*j=r*ip+δ*ip₀)
    (hFit : a*t=r^2+δ*w) :
    d=0 ∧ p≠q := by
  have hdiff : (r-d)*(p-q)+δ*p₀=0 := by linear_combination h₀-hp
  have hpq : p-q≠0 := by
    intro hz
    rw [hz, mul_zero, zero_add] at hdiff
    exact hδ hdiff
  have hd : d^2*(p-q)=0 := by
    linear_combination -hInt+a*hj+q*hFit-r*h₀-δ*hw+d*(hp-h₀)
  refine ⟨?_, sub_ne_zero.mp hpq⟩
  by_contra hdn
  exact (pow_ne_zero 2 hdn) ((mul_eq_zero.mp hd).resolve_right hpq)
end Field

end RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicLiveFourth
