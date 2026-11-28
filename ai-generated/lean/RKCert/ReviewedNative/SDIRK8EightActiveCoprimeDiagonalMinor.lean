module

public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveCoprimeDiagonalMinor

open Matrix

/-- A monic cofactor relation makes the square nodal coefficient
determinant vanish. The unit coordinate, rather than a generic
Vandermonde inverse, is the relevant guard. -/
theorem monicCofactorDet {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (v : ι → R) (i : ι)
    (h : M *ᵥ v=0) (hmonic : v i=1) :
    M.det=0 := by
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors h (i := i)
  rw [hmonic]
  exact one_mem _

/-- A field evaluation at an actual candidate annihilates the chosen
multiplication columns while evaluating the first basis vector to
one. Hence the witnessed square maximal minor vanishes. -/
theorem evaluatedMinorVanishing {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (v : ι → R) (i : ι)
    (h : v ᵥ* M=0) (hi : v i=1) :
    M.det=0 := by
  have w : M.transpose *ᵥ v = 0 := by rw [Matrix.mulVec_transpose,h]
  simpa only [Matrix.det_transpose] using monicCofactorDet M.transpose v i w hi

#print axioms monicCofactorDet
#print axioms evaluatedMinorVanishing

end RKCert.ReviewedNative.SDIRK8EightActiveCoprimeDiagonalMinor
