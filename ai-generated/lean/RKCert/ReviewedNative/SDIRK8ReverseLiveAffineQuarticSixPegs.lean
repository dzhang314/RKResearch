module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineQuarticSixPegs

open Polynomial
open scoped Matrix Polynomial BigOperators

/-- Divided-difference read with prescribed scalar moments, truncated at
degree eight. This definition does not require division in the ring. -/
noncomputable def momentRead {R : Type*} [CommRing R] (μ : ℕ → R) : R[X] →ₗ[R] R[X] where
  toFun D := ∑ j ∈ Finset.range 8, D.coeff (j+1) •
    ∑ i ∈ Finset.range (j+1), C (μ (j-i)) * X ^ i
  map_add' D E := by
    simp only [coeff_add, add_smul, Finset.sum_add_distrib]
  map_smul' r D := by
    have hcoeff (j : ℕ) : (r • D).coeff j = r*D.coeff j := by
      rw [smul_eq_C_mul, coeff_C_mul]
    simp only [hcoeff, RingHom.id_apply, mul_smul, Finset.smul_sum]

/-- The coefficient operation is linear in the candidate ordinary nodal
polynomial, without any positive quadratic form or inversion. -/
noncomputable def bezoutMap {R : Type*} [CommRing R]
    (W : R[X] →ₗ[R] R[X]) (L : R[X]) : R[X] →ₗ[R] R[X] where
  toFun D := L * W D - D * W L
  map_add' D E := by simp only [map_add]; ring
  map_smul' r D := by
    change L*W (r • D)-(r • D)*W L = r • (L*W D-D*W L)
    rw [map_smul]
    simp only [smul_eq_C_mul]
    ring

/-- Four low coefficients of the three monic-cofactor basis columns and
the squared numerator column. -/
noncomputable def coefficientMatrix {R : Type*} [CommRing R]
    (f : R[X] →ₗ[R] R[X]) (E Q : R[X]) : Matrix (Fin 4) (Fin 4) R :=
  fun i j => ![(f E).coeff i, (f (X*E)).coeff i, (f (X^2*E)).coeff i, (Q^2).coeff i] j

/-- Six fixed ordinary pegs leave a monic quadratic cofactor. A true
Bezout equality forces the projected four-by-four determinant to vanish,
even when some of its individual columns or leading coefficients vanish. -/
theorem sixPegDetZero {R : Type*} [CommRing R] (f : R[X] →ₗ[R] R[X])
    (E Q : R[X]) (r₀ r₁ lam : R)
    (h : f (E*(C r₀ + C r₁*X + X^2)) = C lam * Q^2) :
    (coefficientMatrix f E Q).det=0 := by
  have hfactor : E*(C r₀ + C r₁*X + X^2) =
      (r₀ • E + r₁ • (X*E)) + X^2*E := by
    simp only [smul_eq_C_mul]
    ring
  rw [hfactor, map_add, map_add, map_smul, map_smul] at h
  let v : Fin 4 → R := ![r₀,r₁,1,-lam]
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors (v := v) (i := 2)
  · funext i
    have hc := congrArg (fun D : R[X] => D.coeff (i : ℕ)) h
    simp only [coeff_add, smul_eq_C_mul, coeff_C_mul] at hc
    change (∑ j, coefficientMatrix f E Q i j * v j) = 0
    simp [Fin.sum_univ_succ, coefficientMatrix, v]
    linear_combination hc
  ·
    simp [v]

#print axioms momentRead
#print axioms bezoutMap
#print axioms sixPegDetZero

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineQuarticSixPegs
