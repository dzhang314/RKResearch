module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticNoHole

/-- Four genuinely paid ordinary moments force a degree-at-most-four
polynomial onto the shifted Legendre quartic. These are the four rows
of the rational inverse Hilbert matrix, with no order or positivity. -/
theorem quarticMomentRigid {K : Type*} [Field K] [CharZero K]
    (a b c d e : K)
    (h₀ : a+b/2+c/3+d/4+e/5=0)
    (h₁ : a/2+b/3+c/4+d/5+e/6=0)
    (h₂ : a/3+b/4+c/5+d/6+e/7=0)
    (h₃ : a/4+b/5+c/6+d/7+e/8=0) :
    a=e/70 ∧ b=-(2*e/7) ∧ c=9*e/7 ∧ d=-(2*e) := by
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination 16*h₀-120*h₁+240*h₂-140*h₃
  · linear_combination -120*h₀+1200*h₁-2700*h₂+1680*h₃
  · linear_combination 240*h₀-2700*h₁+6480*h₂-4200*h₃
  · linear_combination -140*h₀+1680*h₁-4200*h₂+2800*h₃

/-- A genuine affine right-hand side has two remainder columns; the
second one is not removed by borrowing a constant-numerator identity.
This identity can be used directly in the polynomial ring. -/
theorem affineReadRemainder {R : Type*} [CommRing R]
    (L D WD WL V R₀ R₁ V₁ X p₀ p₁ : R)
    (hV : WL*V=1+L*R₀) (hXV : X*V=L*R₁+V₁)
    (h : L*WD-D*WL=p₀+p₁*X) :
    D=L*(WD*V-D*R₀-p₁*R₁)-p₀*V-p₁*V₁ := by
  linear_combination -V*h-D*hV-p₁*hXV

/-- Two high interpolation coefficients determine the two affine
residue scales, without assuming a formal generic pivot. -/
theorem twoColumnPivot {R : Type*} [CommRing R]
    (a b c d r s : R) (h₀ : a*r+b*s=0) (h₁ : c*r+d*s = -1) :
    (a*d-b*c)*r=b ∧ (a*d-b*c)*s = -a := by
  constructor
  · linear_combination d*h₀-b*h₁
  · linear_combination a*h₁-c*h₀

/-- The actual first backward equation at penultimate gives equal
ordinary weights for the terminal and penultimate. -/
theorem actualTerminalWeightsEqual {R : Type*} [CommRing R] [NoZeroDivisors R]
    (u b₉ b₁₀ : R) (hu : u≠0)
    (h : b₉+b₁₀*u=b₉*(1+u)) : b₉=b₁₀ := by
  have hz : u*(b₉-b₁₀)=0 := by linear_combination -h
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hu)

/-- The equality of ordinary weights is a division-free cardinal gate. -/
theorem penultimateCardinalGate {R : Type*} [CommRing R]
    (c₀ x₀ d₉ d₁₀ b₉ b₁₀ : R)
    (hc : c₀=b₉*d₉) (hx : x₀=b₁₀*d₁₀) (h : b₉=b₁₀) :
    c₀*d₁₀-x₀*d₉=0 := by
  rw [hc,hx,h]
  ring

#print axioms quarticMomentRigid
#print axioms affineReadRemainder
#print axioms twoColumnPivot
#print axioms actualTerminalWeightsEqual
#print axioms penultimateCardinalGate

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticNoHole
