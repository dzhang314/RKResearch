module

public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8NormProjection
open scoped Matrix

/-- Evaluation at an actual tail gap annihilates multiplication by a
vanishing profile residual. Its constant-coordinate read is one, so the
multiplication determinant vanishes, even for a reducible tail polynomial. -/
theorem normProjectionOfEvaluation {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (e : n → K) (j : n) (hj : e j = 1)
    (h : e ᵥ* M = 0) :
    M.det = 0 := by
  by_contra hm
  have hz : e = 0 := Matrix.eq_zero_of_vecMul_eq_zero hm h
  have hjz : e j = 0 := congrFun hz j
  exact one_ne_zero (hj.symm.trans hjz)

#print axioms normProjectionOfEvaluation

end RKCert.ReviewedNative.SDIRK8NormProjection
