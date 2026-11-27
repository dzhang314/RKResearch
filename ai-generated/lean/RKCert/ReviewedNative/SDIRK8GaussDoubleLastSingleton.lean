module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8GaussDoubleLastSingleton

/-- Eliminating the unknown affine reverse-root location from the
all-singleton arithmetic tail gives a scalar condition independent
of the extra silent clock. -/
theorem arithmeticTailElimination {K : Type*} [Field K]
    (x c d z k H T p₀ p₁ p₂ : K)
    (h₀ : x-z ≠ 0) (hshape : d=2*c-x)
    (h₁ : (x-z)*p₁=k*(c-z)*p₀)
    (h₂ : H*(x-z)*p₂= -k*T*(d-z)*p₀) :
    H*p₂+2*T*p₁-k*T*p₀=0 := by
  have hh : (H*p₂+2*T*p₁-k*T*p₀)*(x-z)=0 := by
    linear_combination h₂+2*T*h₁-k*T*p₀*hshape
  exact (mul_eq_zero.mp hh).resolve_right h₀

def readCubic {R : Type*} [CommRing R] (a b c d x : R) : R :=
  a+b*x+c*x^2+d*x^3

/-- The root-free reflected star cut is cubic in the common diagonal.
Its three forbidden gap factors are precisely the literal tail
clock collisions, not modular padding assumptions. -/
theorem starTailElimination {K : Type*} [Field K]
    (x z g v a b c d : K)
    (hroot : x-z ≠ 0) (hguard : (2:K)*v*(v^2-1) ≠ 0)
    (hminus : (x-z)*readCubic a b c d (x-g-g*v) =
      (2-v^2)*(x-g-g*v-z)*readCubic a b c d x)
    (hplus : (x-z)*readCubic a b c d (x-g+g*v) =
      (2-v^2)*(x-g+g*v-z)*readCubic a b c d x) :
    d*g^3+g^2*(c+3*d*(x-g))+readCubic a b c d x=0 := by
  simp only [readCubic] at hminus hplus ⊢
  have h : ((1-v)*(a+b*(x-g-g*v)+c*(x-g-g*v)^2+d*(x-g-g*v)^3)
      -(1+v)*(a+b*(x-g+g*v)+c*(x-g+g*v)^2+d*(x-g+g*v)^3)
      +2*v*(2-v^2)*(a+b*x+c*x^2+d*x^3))*(x-z)=0 := by
    linear_combination (1-v)*hminus-(1+v)*hplus
  have h' : (d*g^3+g^2*(c+3*d*(x-g))+(a+b*x+c*x^2+d*x^3))*
      (2*v*(v^2-1))=0 := by
    have hh := (mul_eq_zero.mp h).resolve_right hroot
    linear_combination -hh
  exact (mul_eq_zero.mp h').resolve_right hguard

/-- A still-unknown physical defect can be eliminated from two
literal affine reads without assuming either slope is a unit. -/
theorem affineDefectCut {R : Type*} [CommRing R]
    (h a b c d : R) (h₀ : a+b*h=0) (h₁ : c+d*h=0) :
    a*d-b*c=0 := by
  linear_combination d*h₀-b*h₁

#print axioms arithmeticTailElimination
#print axioms starTailElimination
#print axioms affineDefectCut

end RKCert.ReviewedNative.SDIRK8GaussDoubleLastSingleton
