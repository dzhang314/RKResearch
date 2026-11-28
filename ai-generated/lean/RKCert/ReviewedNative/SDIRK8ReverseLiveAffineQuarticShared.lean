module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineQuarticShared

/-- A genuine ordinary zero of the affine reverse numerator has zero
cubic defect; the ordinarily silent reverse-live row is not substituted. -/
theorem actualOrdinaryHole {R : Type*} [CommRing R] [NoZeroDivisors R]
    (b h μ r z w : R) (hb : b≠0) (hw : w=0)
    (hpair : b*h=μ*(r-z)*w) : h=0 := by
  rw [hw,mul_zero] at hpair
  exact (mul_eq_zero.mp hpair).resolve_left hb

/-- Cancel only the actual distinct Gaussian hole from the ordinary
nodal derivative. The remaining nodes have the same constant read. -/
theorem deflatedConstantRead {R : Type*} [CommRing R] [NoZeroDivisors R]
    (c r d₇ b h μ τ : R) (hcr : c≠r)
    (hread : ((c-r)*d₇)*b*h=μ*(τ*(c-r))) :
    d₇*b*h=μ*τ := by
  have h₀ : (c-r)*(d₇*b*h-μ*τ)=0 := by linear_combination hread
  exact sub_eq_zero.mp ((mul_eq_zero.mp h₀).resolve_left (sub_ne_zero.mpr hcr))

/-- The starred rear equation for a genuine cubic profile has exactly
the three literal collision factors, unless its scalar quotient is zero. -/
theorem starCubicTail {R : Type*} [CommRing R]
    (p₃ p₂ p₁ p₀ X u : R) :
    let P := fun v : R => p₃*v^3+p₂*v^2+p₁*v+p₀
    (2-u)*P (X-u)-u*P (X-2+u)+(2*u-2)*(1+2*u-u^2)*P X =
      -2*u*(u-1)*(u-2)*(P X+(3*X-2)*p₃+p₂) := by
  dsimp
  ring

/-- A six-peg signed mask with one actual ordinary nonhole remaining
supplies homogeneous coefficients without inverting a residue pivot. -/
theorem oneMissingMask {R : Type*} [CommRing R] [NoZeroDivisors R]
    (b f E m₀ m₁ : R) (hb : b≠0) (hE : E≠0)
    (h₀ : m₀=b*E) (h₁ : m₁=b*f*E) :
    m₀≠0 ∧ m₁=f*m₀ := by
  constructor
  · rw [h₀]
    exact mul_ne_zero hb hE
  · rw [h₀,h₁]
    ring

#print axioms actualOrdinaryHole
#print axioms deflatedConstantRead
#print axioms starCubicTail
#print axioms oneMissingMask

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineQuarticShared
