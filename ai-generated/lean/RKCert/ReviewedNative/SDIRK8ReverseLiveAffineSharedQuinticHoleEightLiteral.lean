module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleEightLiteral

/-- The fixed arithmetic hole-eight cubic has no zero gap, no k=0,
and no terminal double gap over a characteristic-zero field. -/
theorem arithmeticGapUnits {K : Type*} [Field K] [CharZero K] (u : K)
    (h : 2+3*u-12*u^2+4*u^3=0) : u≠0 ∧ (1+2*u-u^2)≠0 ∧ u≠2 := by
  refine ⟨?_,?_,?_⟩
  · intro hz
    norm_num [hz] at h
  · intro hk
    have hneg : u = -2 := by linear_combination (4-4*u)*hk-h
    norm_num [hneg] at hk
  · intro ht
    norm_num [ht] at h

/-- Actual ordinarily silent fourth recovery from the true penultimate
comparison with a polynomial profile and a different ordinary hole. -/
theorem recoverActualFourth {R : Type*} [CommRing R] [NoZeroDivisors R]
    (γ u k x c Hc Hx R₀ s : R)
    (hγ : γ≠0) (hu : u≠0) (hk : k≠0) (hHx : Hx≠0)
    (hclock : c=x-γ*u) (hR : u*R₀=Hc-k*Hx)
    (hread : (x-γ*s)*Hc=k*(c-γ*s)*Hx) :
    γ*R₀≠0 ∧ (γ*R₀)*s=x*R₀+γ*k*Hx := by
  have hzero : u*((γ*R₀)*s-(x*R₀+γ*k*Hx))=0 := by
    calc
      u*((γ*R₀)*s-(x*R₀+γ*k*Hx)) =
        -(x-γ*s)*(u*R₀)-γ*u*k*Hx := by ring
      _ = 0 := by
        rw [hR]
        rw [hclock] at hread
        linear_combination -hread
  have hcoord := sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hu)
  refine ⟨mul_ne_zero hγ ?_,hcoord⟩
  intro hz
  simp only [hz,mul_zero,zero_mul,zero_add] at hcoord
  exact (mul_ne_zero (mul_ne_zero hγ hk) hHx) hcoord.symm

/-- The actual fourth polynomial can drop degree. Its homogeneous
evaluation still vanishes at the recovered true coordinate. -/
theorem fourthHomogeneousNoLeading {R : Type*} [CommRing R]
    (J₀ J₁ J₂ s n d : R) (hcoord : d*s=n)
    (hJ : J₀+J₁*s+J₂*s^2=0) :
    J₀*d^2+J₁*n*d+J₂*n^2=0 := by
  rw [← hcoord]
  linear_combination d^2*hJ

#print axioms arithmeticGapUnits
#print axioms recoverActualFourth
#print axioms fourthHomogeneousNoLeading

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleEightLiteral
