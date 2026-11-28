module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveStarInteriorReads

/-- Averaging the two actual reverse reads at the star pegs solves for
the invisible clock without choosing a rear sign. Here `K` is the
scaled terminal read and `U` the scaled mean of the rear reads. -/
theorem actualSilentMean {R : Type*} [Field R]
    (x m z K U : R) (hm : x-m≠0) (hK : K≠0)
    (h : (x-z)*U=K*(m-z)) :
    K-U≠0 ∧ z*(K-U)=m*K-x*U := by
  have h0 : z*(K-U)=m*K-x*U := by linear_combination h
  refine ⟨?_,h0⟩
  intro h1
  have h2 : K=U := sub_eq_zero.mp h1
  have h3 : (x-m)*K=0 := by
    rw [← h2] at h
    linear_combination h
  exact (mul_ne_zero hm hK) h3

/-- Two rows annihilating the true missing monic quadratic give a
cofactor vector proportional to that same quadratic, including
the case of zero leading cofactor. -/
theorem missingMonicQuadraticCofactors {R : Type*} [CommRing R]
    (a b c d e f u v : R) (h₁ : a*u+b*v+c=0) (h₂ : d*u+e*v+f=0) :
    b*f-c*e=(a*e-b*d)*u ∧ c*d-a*f=(a*e-b*d)*v := by
  constructor
  · linear_combination b*h₂-e*h₁
  · linear_combination d*h₁-a*h₂

/-- The ordinary peg product can be folded with a single cleared gap word.
This identity does not invert `B` within any residue algebra. -/
theorem foldedStarFactor {R : Type*} [CommRing R]
    (X m γ A B w : R) (h : A+B*w=0) :
    B*((X-m)^2-γ^2*w)=B*(X-m)^2+γ^2*A := by
  linear_combination -(γ^2)*h

/-- Evaluating the sixth-degree padded fifth-row polynomial at an actual
scaled clock is equivalent after multiplying by the sixth power of the
scale. In particular the cleared implication works without a fraction
or any claim that its reduction has nonzero scale. -/
theorem clearedSixthEvaluation {R : Type*} [CommRing R]
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ D N y : R) (h : N=D*y) :
    a₀*D^6+a₁*N*D^5+a₂*N^2*D^4+a₃*N^3*D^3+a₄*N^4*D^2+a₅*N^5*D+a₆*N^6 =
      D^6*(a₀+a₁*y+a₂*y^2+a₃*y^3+a₄*y^4+a₅*y^5+a₆*y^6) := by
  rw [h]
  ring

#print axioms actualSilentMean
#print axioms missingMonicQuadraticCofactors
#print axioms foldedStarFactor
#print axioms clearedSixthEvaluation

end RKCert.ReviewedNative.SDIRK8EightActiveStarInteriorReads
