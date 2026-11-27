module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8GaussDoubleSilentTail

/-- Transport of an affine pure profile to the only silent coordinate
at the terminal clock, even when the two active h amplitudes differ. -/
theorem silentAffineFromPair {K : Type*} [Field K]
    (a b s h₀ h₁ h₂ v₀ v₁ v₂ q : K)
    (hs : s≠0)
    (h₀r : v₀=q*h₀) (h₁r : v₁=q*h₁)
    (h : a*h₀+b*h₁+s*h₂=0)
    (v : a*v₀+b*v₁+s*v₂=0) : v₂=q*h₂ := by
  rw [h₀r,h₁r] at v
  have z : s*(v₂-q*h₂)=0 := by linear_combination v-q*h
  exact sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_left hs)

#print axioms silentAffineFromPair

end RKCert.ReviewedNative.SDIRK8GaussDoubleSilentTail
