module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8GaussDoubleReverseProjection

/-- When the physical silent copy of the terminal clock precedes both
last nonterminal active rows, the reverse basis reads at those two
rows come from the terminal row alone. No ratio of cubic defects
(or of the two nonterminal clock gaps) is taken. -/
theorem activeEighthRatio {K : Type*} [Field K]
    (g u v b₈ b₉ b₁₀ h₈ h₉ a₈ a₉ β w : K)
    (hb₈ : b₈ ≠ 0) (hb₉ : b₉ ≠ 0) (hb₁₀ : b₁₀ ≠ 0)
    (h₈read : b₈*h₈ = β*w*a₈)
    (h₉read : b₉*h₉ = β*w*a₉)
    (h₈tap : b₁₀*a₈ = b₈*g*v)
    (h₉tap : b₁₀*a₉ = b₉*g*u) :
    u*h₈ = v*h₉ := by
  have h₈' : b₁₀*h₈ = β*w*g*v := by
    have h : (b₁₀*h₈ - β*w*g*v)*b₈ = 0 := by
      linear_combination b₁₀*h₈read + β*w*h₈tap
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hb₈)
  have h₉' : b₁₀*h₉ = β*w*g*u := by
    have h : (b₁₀*h₉ - β*w*g*u)*b₉ = 0 := by
      linear_combination b₁₀*h₉read + β*w*h₉tap
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hb₉)
  have h : (u*h₈-v*h₉)*b₁₀=0 := by
    linear_combination u*h₈' - v*h₉'
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hb₁₀)

/-- If the sole silent balancing stage is the physical eighth,
its actual weighted successor taps give the penultimate ratio.
In particular no reflected normalization at the zero weight is
part of the hypotheses. -/
theorem silentEighthRatio {K : Type*} [Field K]
    (g u b₉ b₁₀ h₉ h₁₀ a₈ a₉ α β w : K)
    (hg : g ≠ 0) (hb₉ : b₉ ≠ 0) (hb₁₀ : b₁₀ ≠ 0) (hw : w ≠ 0)
    (hterminalW : w = -(g*g*b₁₀))
    (hterminal : b₁₀*h₁₀ = α*w)
    (hsil : 0 = -α*w+β*w*a₈)
    (hbal : -w = 2*g*u*b₁₀*a₈)
    (h₉read : b₉*h₉ = β*w*a₉)
    (h₉tap : b₁₀*a₉ = b₉*g*u) :
    h₉ = 2*u^2*h₁₀ := by
  have ha : α=β*a₈ := by
    have h : (α-β*a₈)*w=0 := by linear_combination hsil
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hw)
  have h₈' : 2*u*a₈=g := by
    have h : (2*u*a₈-g)*(g*b₁₀)=0 := by
      linear_combination -hbal-hterminalW
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (mul_ne_zero hg hb₁₀))
  have h₉' : b₁₀*h₉ = β*w*g*u := by
    have h : (b₁₀*h₉ - β*w*g*u)*b₉ = 0 := by
      linear_combination b₁₀*h₉read + β*w*h₉tap
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hb₉)
  rw [ha] at hterminal
  have h : (h₉ - 2*u^2*h₁₀)*b₁₀=0 := by
    linear_combination h₉' - 2*u^2*hterminal - β*w*u*h₈'
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hb₁₀)

/-- Denominator-free linear/quadric elimination for the arithmetic
tail, usable even in the zero coefficient branches (where it is not
asserted to recover the root). -/
theorem linearQuadraticProjection {R : Type*} [CommRing R]
    (u a b c l m : R)
    (hq : a*u^2+b*u+c=0) (hl : l+m*u=0) :
    a*l^2-b*l*m+c*m^2=0 := by
  linear_combination m^2*hq+(a*(l-m*u)-b*m)*hl

def cubicRead {K : Type*} [CommRing K] (a b c d x : K) : K :=
  a+b*x+c*x^2+d*x^3

/-- Subtract the two literal reflected star equations to obtain the
odd cubic read, then use it in their sum. In particular the result
is affine in the squared gap, without taking a square root. -/
theorem starCubicSymmetricCut {K : Type*} [Field K]
    (x y z g v a b c d : K)
    (h₂ : (2:K) ≠ 0) (hgap : 2*g*v ≠ 0) (hz : x-z ≠ 0)
    (hPlus : (x-z)*cubicRead a b c d (y+g*v) =
      (2-v^2)*(y+g*v-z)*cubicRead a b c d x)
    (hMinus : (x-z)*cubicRead a b c d (y-g*v) =
      (2-v^2)*(y-g*v-z)*cubicRead a b c d x) :
    c*g^2*v^2+d*(2*y+z)*g^2*v^2 +
      cubicRead a b c d y-(y-z)*(b+2*c*y+3*d*y^2)=0 := by
  simp only [cubicRead] at hPlus hMinus ⊢
  have hOdd : (x-z)*(b+2*c*y+3*d*y^2+d*g^2*v^2) =
      (2-v^2)*(a+b*x+c*x^2+d*x^3) := by
    have h : ((x-z)*(b+2*c*y+3*d*y^2+d*g^2*v^2) -
        (2-v^2)*(a+b*x+c*x^2+d*x^3))*(2*g*v)=0 := by
      linear_combination hPlus-hMinus
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hgap)
  have h : (c*g^2*v^2+d*(2*y+z)*g^2*v^2 +
      (a+b*y+c*y^2+d*y^3)-(y-z)*(b+2*c*y+3*d*y^2))*(2*(x-z))=0 := by
    linear_combination hPlus+hMinus-2*(y-z)*hOdd
  exact (mul_eq_zero.mp h).resolve_right (mul_ne_zero h₂ hz)

#print axioms activeEighthRatio
#print axioms silentEighthRatio
#print axioms linearQuadraticProjection
#print axioms starCubicSymmetricCut

end RKCert.ReviewedNative.SDIRK8GaussDoubleReverseProjection
