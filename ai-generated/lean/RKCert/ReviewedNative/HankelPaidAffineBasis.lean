module

public import RKCert.ReviewedNative.StagePolynomialMoment
public import RKCert.ReviewedNative.HankelPaidMonicBasis
public import RKCert.ReviewedNative.NodalPaidHankel

import Mathlib.Tactic.Ring

@[expose] public section

/-! # Affine invariance of the actual one-mask polynomial readout

Translation uses the monic shifted-power basis, scaling uses diagonal
matrices with nonzero determinant, and the mask contributes just one
nonzero scalar. Neither positivity, quadrature order, nor a cover is
needed for this coordinate equality. -/
namespace RKResearch.Certified.Graded.HankelPaidAffineBasis

open Matrix Polynomial Module HankelPaidMonicBasis
open scoped Polynomial Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

def affineClock (a d x : K) : K := a*x+d

theorem affineClock_injective {a d : K} (ha : a ≠ 0) :
    Function.Injective (affineClock a d) := by
  intro x y h
  apply mul_left_cancel₀ ha
  exact add_right_cancel h

def affineClockMask (a d : K) (U : Finset K) : K[X] := by
  classical
  exact cutNodalPolynomial (U.image (affineClock a d))

/-- One mask contributes a single factor a^|U|, not its square. -/
theorem eval_affineClockMask {a d : K} (ha : a ≠ 0) (U : Finset K) (x : K) :
    (affineClockMask a d U).eval (affineClock a d x) =
      a^U.card * (cutNodalPolynomial U).eval x := by
  classical
  unfold affineClockMask cutNodalPolynomial
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_image (affineClock_injective (d := d) ha).injOn]
  calc
    _ = ∏ t ∈ U, a*(x-t) := by
      apply Finset.prod_congr rfl
      intro t _
      unfold affineClock
      ring
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]

variable {ι : Type*} [Fintype ι]

def maskedStageMoment (x b : ι → K) (P : K[X]) : K[X] →ₗ[K] K :=
  (weightedStageMoment x b).comp (LinearMap.mulLeft K P)

@[simp] theorem maskedStageMoment_apply (x b : ι → K) (P Q : K[X]) :
    maskedStageMoment x b P Q = ∑ t, b t * (P.eval (x t) * Q.eval (x t)) := by
  change weightedStageMoment x b (P*Q) = _
  simp only [weightedStageMoment_apply, Polynomial.eval_mul]

/-- Full-width affine Gram comparison, valid for arbitrary signed
weights, arbitrary numbers of paid powers and an arbitrary finite mask. -/
theorem rank_affine_hankel_eq_original (x b : ι → K) {a d : K} (ha : a ≠ 0)
    (U : Finset K) (n : ℕ) :
    (hankel (maskedStageMoment (fun t => affineClock a d (x t)) b
      (affineClockMask a d U)) n).rank =
    (hankel (maskedStageMoment x b (cutNodalPolynomial U)) n).rank := by
  let raw := maskedStageMoment x b (cutNodalPolynomial U)
  let B : Fin n → K[X] := fun i => (X+C (d/a))^i.val
  let D : Matrix (Fin n) (Fin n) K := Matrix.diagonal (fun i => a^i.val)
  have bm (i : Fin n) : (B i).Monic := (monic_X_add_C (d/a)).pow i.val
  have bd (i : Fin n) : (B i).natDegree=i.val := natDegree_pow_X_add_C i.val (d/a)
  have nd : D.det ≠ 0 := by
    change (Matrix.diagonal (fun i : Fin n => a^i.val)).det ≠ 0
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero i.val ha)
  have linear (t : ι) : affineClock a d (x t) = a*(x t+d/a) := by
    unfold affineClock
    rw [mul_add, mul_div_cancel₀ _ ha]
  have entries :
      hankel (maskedStageMoment (fun t => affineClock a d (x t)) b (affineClockMask a d U)) n =
       (a^U.card) • ((D*pairGram raw B B)*D) := by
    funext i j
    change _ = (a^U.card)*((D*pairGram raw B B)*D) i j
    unfold D
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hankel_apply, maskedStageMoment_apply]
    change _ = a^U.card * ((a^i.val * raw (B i * B j))*a^j.val)
    unfold raw
    rw [maskedStageMoment_apply]
    simp only [eval_affineClockMask ha]
    simp only [B, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, linear, mul_pow, pow_add,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [entries, Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero U.card ha)),
    Matrix.rank_mul_eq_left_of_det_ne_zero D _ nd,
    Matrix.rank_mul_eq_right_of_det_ne_zero D _ nd]
  exact rank_pairGram_of_monic_degrees raw B bm bd

/-- The uncentered evaluation Hankel is exactly the reviewed paid map
in `degreeLTEquiv` coordinates. Equality of ranks is not estimated. -/
theorem rank_hankel_eq_nodal {s : ℕ} (A : Matrix (Fin s) (Fin s) K)
    (b : Fin s → K) (P : K[X]) (q : ℕ) :
    (hankel (maskedStageMoment (nodes A) b P) (q+1)).rank =
      finrank K (nodalPaidHankel A b P q).range := by
  let H := hankel (maskedStageMoment (nodes A) b P) (q+1)
  let E := degreeLTEquiv K (q+1)
  have e (j : Fin (q+1)) :
      E.symm (Pi.single j 1) = ⟨monomial j.val 1, monomial_coe_mem_degreeLT j 1⟩ := by
    apply E.injective
    rw [E.apply_symm_apply]
    funext i
    change (Pi.single j (1 : K) : Fin (q+1) → K) i = (monomial j.val (1:K)).coeff i.val
    by_cases h : i=j
    · subst i
      simp
    · have hi : i.val ≠ j.val := fun h' => h (Fin.ext h')
      simp [Pi.single_apply, h, Ne.symm h, coeff_monomial, hi, Ne.symm hi]
  have hm : H.mulVecLin = (nodalPaidHankel A b P q).comp E.symm.toLinearMap := by
    apply (Pi.basisFun K (Fin (q+1))).ext
    intro j
    funext i
    rw [Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
      Matrix.col_apply, LinearMap.comp_apply]
    change H i j = nodalPaidHankel A b P q (E.symm (Pi.single j 1)) i
    rw [e j, nodalPaidHankel_monomial]
    unfold H
    rw [hankel_apply, maskedStageMoment_apply]
    simp only [Polynomial.eval_pow, Polynomial.eval_X, ← mul_assoc]
  change finrank K H.mulVecLin.range = _
  rw [hm, LinearEquiv.range_comp]

/-- Generic checked-target form: the centered matrix and the actual
nodal readout have equal rank, for every width, without a cover. -/
theorem rank_affine_hankel_eq_nodal {s : ℕ} (A : Matrix (Fin s) (Fin s) K)
    (b : Fin s → K) {a d : K} (ha : a ≠ 0) (U : Finset K) (q : ℕ) :
    (hankel (maskedStageMoment (fun t => affineClock a d (nodes A t)) b
      (affineClockMask a d U)) (q+1)).rank =
    finrank K (nodalPaidHankel A b (cutNodalPolynomial U) q).range :=
  (rank_affine_hankel_eq_original (nodes A) b ha U (q+1)).trans
    (rank_hankel_eq_nodal A b (cutNodalPolynomial U) q)

end
end RKResearch.Certified.Graded.HankelPaidAffineBasis
