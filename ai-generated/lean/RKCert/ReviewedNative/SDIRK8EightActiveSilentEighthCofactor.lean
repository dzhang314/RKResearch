module

public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveSilentEighthCofactor

open Matrix

/-- The scaled missing-clock coefficients are valid at a monic
solution even without a pivot unit. -/
theorem cofactorScale {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (x : ι → R) :
    A.cramer (A *ᵥ x) = A.det • x := by
  rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
    Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- A singular selected pivot gives the zero cofactor vector rather
than requiring a choice of pivot at an actual root. -/
theorem singularCofactorAtSolution {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (x b : ι → R) (h : A *ᵥ x=b) (hz : A.det=0) :
    A.cramer b=0 := by
  rw [←h, cofactorScale, hz, zero_smul]

#print axioms cofactorScale
#print axioms singularCofactorAtSolution

end RKCert.ReviewedNative.SDIRK8EightActiveSilentEighthCofactor
