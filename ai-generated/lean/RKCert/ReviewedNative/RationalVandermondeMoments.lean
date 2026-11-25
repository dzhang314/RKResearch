module

public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Field.Rat

@[expose] public section

/-! Source-only candidate: the one transposed Vandermonde solve used by
both rational donor rows and terminal perturbation-copy weights. -/

namespace RKResearch.Certified.RationalMoments

open scoped BigOperators Matrix

variable {n : ℕ}

noncomputable def momentSolve (z m : Fin n → ℚ) : Fin n → ℚ :=
  ((Matrix.vandermonde z)ᵀ)⁻¹ *ᵥ m

theorem momentSolve_spec {z : Fin n → ℚ} (inj : Function.Injective z)
    (m : Fin n → ℚ) (k : Fin n) :
    (∑ i, momentSolve z m i * z i ^ k.val) = m k := by
  let V := (Matrix.vandermonde z)ᵀ
  have hu : IsUnit V.det := by
    change IsUnit ((Matrix.vandermonde z)ᵀ).det
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr inj)
  have e : V *ᵥ momentSolve z m = m := by
    change V *ᵥ (V⁻¹ *ᵥ m) = m
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv V hu, Matrix.one_mulVec]
  simpa only [V, Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply, Matrix.vandermonde_apply,
    mul_comm] using congrFun e k

noncomputable def primitiveWeights (z : Fin n → ℚ) (x : ℚ) : Fin n → ℚ :=
  momentSolve z (fun k => x ^ (k.val + 1) / ((k.val + 1 : ℕ) : ℚ))

theorem primitiveWeights_spec {z : Fin n → ℚ} (inj : Function.Injective z)
    (x : ℚ) (k : Fin n) :
    (∑ i, primitiveWeights z x i * z i ^ k.val) =
      x ^ (k.val + 1) / ((k.val + 1 : ℕ) : ℚ) :=
  momentSolve_spec inj _ k

noncomputable def terminalCopyWeights (lam : Fin n → ℚ) (β a : ℚ) : Fin n → ℚ :=
  momentSolve lam (fun k => if k.val = 0 then β else if k.val = 1 then a else 0)

theorem terminalCopyWeights_spec {lam : Fin n → ℚ} (inj : Function.Injective lam)
    (β a : ℚ) (k : Fin n) :
    (∑ l, terminalCopyWeights lam β a l * lam l ^ k.val) =
      if k.val = 0 then β else if k.val = 1 then a else 0 :=
  momentSolve_spec inj _ k

end RKResearch.Certified.RationalMoments
