module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Scalar gates for the unequal-residual repeat of the first clock -/

namespace RKResearch.Certified.SDIRKEightRepeatedFirst

theorem subtract_terminal_reads {R : Type*} [CommRing R]
    {y₀ y₁ y₂ s₀ s₁ s₂ H B h r q : R}
    (a₀ : y₀=H*s₀+H*B*(H-h))
    (a₁ : y₁=H*s₁+H*B*(H*r-h))
    (a₂ : y₂=H*s₂+H*B*(H*q-h)) :
    H*((s₁-s₀)*(q-1)-(s₂-s₀)*(r-1))=
      (y₁-y₀)*(q-1)-(y₂-y₀)*(r-1) := by
  linear_combination (q-1)*(a₀-a₁)+(r-1)*(a₂-a₀)

theorem repeated_quartic_vieta {K : Type*} [Field K]
    {g h a b ℓ : K} (hne : g≠h) (hg : ℓ=g*(a+b*g)) (hh : ℓ=h*(a+b*h)) :
    ℓ+b*g*h=0 := by
  have h : (g-h)*(a+b*(g+h))=0 := by linear_combination hh-hg
  have e := (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)
  linear_combination hg+g*e

theorem repeated_quintic_pivot {K : Type*} [Field K]
    {g h ℓ q : K} (hne : g≠h)
    (hg : (h-g)*ℓ-h*g*(g-h)*q=0) : ℓ+h*g*q=0 := by
  have he : (g-h)*(ℓ+h*g*q)=0 := by linear_combination -hg
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hne)

theorem singular_midpoint_gap {R : Type*} [CommRing R] {v n : R}
    (hn : 5*n=12) (he : v-n+(2-v)*(n-1)=0) : 2*(v-1)=0 := by
  linear_combination -5*he-(v-1)*hn

theorem singular_slope_reduction {K : Type*} [Field K] {m v : K}
    (hm : 32*m^2-224*m+371=0)
    (hv : 7*((m-2)^2+v)=3*m^2) :
    56*v=147 := by
  linear_combination 8*hv-hm

end RKResearch.Certified.SDIRKEightRepeatedFirst
