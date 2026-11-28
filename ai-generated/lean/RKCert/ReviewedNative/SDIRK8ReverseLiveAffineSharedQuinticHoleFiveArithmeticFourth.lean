module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveArithmeticFourth

/-- Exact polynomial divisibility modulo the whole literal fifth cubic
licenses cancellation at the actual point. It says nothing about inverting
the diagonal norm or excluding another root in the same fiber. -/
theorem actualFifthCubicGuardCancellation {F : Type*} [Field F]
    (Y Q A Q₀ E : F) (hD : Y^3-9*Y^2+18*Y-6=0) (hA : A ≠ 0)
    (hfactor : Q-A^2*Q₀=(Y^3-9*Y^2+18*Y-6)*E) (hQ : Q=0) :
    Q₀=0 := by
  apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 2 hA)
  linear_combination hQ-hfactor-E*hD

#print axioms actualFifthCubicGuardCancellation

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveArithmeticFourth
