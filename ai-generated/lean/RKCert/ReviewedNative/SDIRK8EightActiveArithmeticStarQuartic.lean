module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveArithmeticStarQuartic

/-- The arithmetic literal normalized gap is the unit \(1+2t\),
with inverse \(2t-1\), using only \(2t^2=1\). -/
theorem arithmeticLiteralGapUnit {R : Type*} [CommRing R] (t : R) (ht : 2*t^2=1) :
    (1+2*t)*(2*t-1)=1 := by linear_combination 2*ht

/-- Division of the centered quartic by the unordered star pair,
written as an exact identity over any coefficient ring. -/
theorem centeredQuarticDivision {R : Type*} [CommRing R]
    (r₀ r₁ r₂ r₃ r₄ T w : R) :
    r₀+r₁*T+r₂*T^2+r₃*T^3+r₄*T^4 =
      (T^2-w)*(r₄*T^2+r₃*T+r₂+w*r₄)
         +(r₀+w*r₂+w^2*r₄)+T*(r₁+w*r₃) := by ring

/-- The two true opposite roots force both remainder coefficients to
vanish. Distinct actual roots are the only cancellation used here. -/
theorem centeredOppositeRoots {R : Type*} [Field R]
    (r₀ r₁ r₂ r₃ r₄ T w : R) (ht : T^2=w) (hsep : (2:R)*T≠0)
    (hp : r₀+r₁*T+r₂*T^2+r₃*T^3+r₄*T^4=0)
    (hm : r₀+r₁*(-T)+r₂*(-T)^2+r₃*(-T)^3+r₄*(-T)^4=0) :
    (r₀+w*r₂+w^2*r₄=0) ∧ (r₁+w*r₃=0) := by
  have e₁ := centeredQuarticDivision r₀ r₁ r₂ r₃ r₄ T w
  have e₂ := centeredQuarticDivision r₀ r₁ r₂ r₃ r₄ (-T) w
  have ht' : (-T)^2=w := by simpa using ht
  rw [hp,ht,sub_self,zero_mul,zero_add] at e₁
  rw [hm,ht',sub_self,zero_mul,zero_add] at e₂
  have h2 : (2:R)≠0 := by
    intro h
    exact hsep (by simp [h])
  have he : (2:R)*(r₀+w*r₂+w^2*r₄)=0 := by linear_combination -e₁-e₂
  have ho : ((2:R)*T)*(r₁+w*r₃)=0 := by linear_combination -e₁+e₂
  exact ⟨(mul_eq_zero.mp he).resolve_left h2,(mul_eq_zero.mp ho).resolve_left hsep⟩

/-- Homogeneous fixed-quartic remainder conditions after paying the
actual scalar star tail. No inverse of the rear coefficient is used. -/
theorem homogeneousRearRemainders {R : Type*} [CommRing R]
    (r₀ r₁ r₂ r₃ r₄ γ A B w : R)
    (h : A+B*w=0)
    (h1 : r₁+γ^2*w*r₃=0) (h0 : r₀+γ^2*w*r₂+γ^4*w^2*r₄=0) :
    (B*r₁-γ^2*A*r₃=0) ∧ (B^2*r₀-γ^2*A*B*r₂+γ^4*A^2*r₄=0) := by
  constructor
  · linear_combination B*h1-γ^2*r₃*h
  · linear_combination B^2*h0-(γ^2*B*r₂+γ^4*r₄*(B*w-A))*h

/-- An actual ordinary missing node is not either rear peg. Its
homogeneous quadratic read follows without inverting any residue
value or choosing the sign of the rear gap. -/
theorem actualMissingQuadratic {R : Type*} [Field R]
    (r₀ r₁ r₂ r₃ r₄ γ A B w T : R) (h : A+B*w=0)
    (h1 : r₁+γ^2*w*r₃=0) (h0 : r₀+γ^2*w*r₂+γ^4*w^2*r₄=0)
    (hT : T^2-γ^2*w≠0)
    (hR : r₀+r₁*T+r₂*T^2+r₃*T^3+r₄*T^4=0) :
    B*r₄*T^2+B*r₃*T+B*r₂-γ^2*A*r₄=0 := by
  have q := centeredQuarticDivision r₀ r₁ r₂ r₃ r₄ T (γ^2*w)
  have z0 : r₀+γ^2*w*r₂+(γ^2*w)^2*r₄=0 := by linear_combination h0
  rw [hR,h1,z0,mul_zero,add_zero,add_zero] at q
  have z1 := (mul_eq_zero.mp q.symm).resolve_left hT
  linear_combination B*z1-γ^2*r₄*h

#print axioms arithmeticLiteralGapUnit
#print axioms centeredQuarticDivision
#print axioms centeredOppositeRoots
#print axioms homogeneousRearRemainders
#print axioms actualMissingQuadratic

end RKCert.ReviewedNative.SDIRK8EightActiveArithmeticStarQuartic
