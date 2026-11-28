module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineQuarticSilentFourth

/-- The actual penultimate comparison reconstructs the actual silent fourth
clock. Its denominator is nonzero as a consequence of the true row and
the nonzero factors, without a generic-tail leading hypothesis. -/
theorem reconstructSilentFourth {R : Type*} [CommRing R] [NoZeroDivisors R]
    (γ u k x c Px Pc Qx Qc r s : R)
    (hγ : γ≠0) (hu : u≠0) (hk : k≠0) (hPx : Px≠0) (hQc : Qc≠0)
    (hclock : c=x-γ*u) (hr : u*r=Pc*Qx-k*Px*Qc)
    (hread : (x-γ*s)*Pc*Qx=k*(c-γ*s)*Px*Qc) :
    γ*r≠0 ∧ (γ*r)*s=x*r+γ*k*Px*Qc := by
  have h₀ : u*((γ*r)*s-(x*r+γ*k*Px*Qc))=0 := by
    calc
      u*((γ*r)*s-(x*r+γ*k*Px*Qc)) =
          -(x-γ*s)*(u*r)-γ*u*k*Px*Qc := by ring
      _ = 0 := by
        rw [hr]
        rw [hclock] at hread
        linear_combination -hread
  have h₁ := sub_eq_zero.mp ((mul_eq_zero.mp h₀).resolve_left hu)
  refine ⟨mul_ne_zero hγ ?_,h₁⟩
  intro hz
  simp only [hz,mul_zero,zero_mul,zero_add] at h₁
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hγ hk) hPx) hQc) h₁.symm

/-- Homogenize the true padded fourth equation at the recovered coordinate.
The quadratic coefficient may vanish. -/
theorem homogeneousFourth {R : Type*} [CommRing R]
    (j₀ j₁ j₂ s n d : R) (hcoord : d*s=n)
    (hrow : j₀+j₁*s+j₂*s^2=0) :
    j₀*d^2+j₁*n*d+j₂*n^2=0 := by
  rw [← hcoord]
  linear_combination d^2*hrow

#print axioms reconstructSilentFourth
#print axioms homogeneousFourth

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineQuarticSilentFourth
