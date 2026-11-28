module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveEarlyDoubleGauss

/-- Both quartic-zero evaluations read the same cubic basis coordinate.
The physical chronology comparison does not need that coordinate inverted. -/
theorem earlyGaussCross {R : Type*} [CommRing R]
    (η hₐ h₄ lₐ l₄ : R) (ha : hₐ=η*lₐ) (h4 : h₄=η*l₄) :
    h₄*lₐ-hₐ*l₄=0 := by
  linear_combination lₐ*h4-l₄*ha

#print axioms earlyGaussCross

end RKCert.ReviewedNative.SDIRK8EightActiveEarlyDoubleGauss
