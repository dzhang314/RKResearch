module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorActualPencil
public import Mathlib.Data.Rat.Cast.Order

import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact density-polynomial slices and rational base change

For fixed trial x each determinant is a polynomial in the density s of
degree at most its matrix size. The other orientation has the same degree
bound. These are exact, uniformly interpreted determinant polynomials.
-/
namespace RKCert.ReviewedNative.ThreeInteriorPencil

open Polynomial Matrix RKCert.ReviewedNative.PolynomialCertificate
open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
open scoped Matrix Polynomial BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def densityAffine (j : ℕ) : K[X] :=
  C (12252240*threeInteriorBaseMoment (j+1)) +
    C (12252240*(threeInteriorBaseMoment j-threeInteriorBaseMoment (j+1)))*X

theorem densityAffine_eval (j : ℕ) (s : K) :
    (densityAffine j).eval s = threeInteriorScaledMoment s (X^j) := by
  rw [threeInteriorScaledMoment_monomial]
  simp only [densityAffine,eval_add,eval_mul,eval_C,eval_X]
  ring

private theorem densityAffine_degree (j : ℕ) : (densityAffine (K := K) j).natDegree ≤ 1 := by
  unfold densityAffine
  exact natDegree_add_le_of_le
    ((natDegree_C (12252240 * threeInteriorBaseMoment (j + 1) : K)).trans_le (Nat.zero_le 1))
    ((natDegree_C_mul_le _ _).trans natDegree_X.le)

def densityDeterminant (n : ℕ) (x : K) : K[X] :=
  (Matrix.of fun i j : Fin n =>
    densityAffine (i.val+j.val+1)-C x*densityAffine (i.val+j.val)).det

theorem densityDeterminant_eval (n : ℕ) (x s : K) :
    (densityDeterminant n x).eval s = determinantAt n s x := by
  unfold densityDeterminant determinantAt
  change Polynomial.evalRingHom s (Matrix.of (fun i j : Fin n =>
    densityAffine (i.val+j.val+1)-C x*densityAffine (i.val+j.val))).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  change (densityAffine (i.val + j.val + 1) - C x * densityAffine (i.val + j.val)).eval s =
    (pencilAt n s x) i j
  simp only [eval_sub, eval_mul, eval_C, densityAffine_eval, pencilAt, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, gramA_apply, gramB_apply]

private theorem det_degree_of_affine (n : ℕ) (M : Matrix (Fin n) (Fin n) K[X])
    (ent : ∀ i j, (M i j).natDegree ≤ 1) : M.det.natDegree ≤ n := by
  rw [Matrix.det_apply']
  apply natDegree_sum_le_of_forall_le
  intro σ _
  have h : (∑ i : Fin n, (M (σ i) i).natDegree) ≤ ∑ _ : Fin n,(1:ℕ) :=
    Finset.sum_le_sum (fun i _ => ent (σ i) i)
  have p : (∏ i : Fin n, M (σ i) i).natDegree ≤ n :=
    (natDegree_prod_le _ _).trans (by simpa using h)
  have scalar : ((Equiv.Perm.sign σ : ℤ) : K[X]).natDegree ≤ 0 := by simp
  simpa only [zero_add] using natDegree_mul_le_of_le scalar p

theorem densityDeterminant_degree (n : ℕ) (x : K) :
    (densityDeterminant n x).natDegree ≤ n := by
  apply det_degree_of_affine
  intro i j
  exact natDegree_sub_le_of_le (densityAffine_degree _)
    ((natDegree_C_mul_le _ _).trans (densityAffine_degree _))

theorem trialDeterminant_degree (n : ℕ) (s : K) :
    (trialDeterminant n s).natDegree ≤ n := by
  apply det_degree_of_affine
  intro i j
  exact natDegree_sub_le_of_le
    ((natDegree_C (gramA n s i j)).trans_le (Nat.zero_le 1))
    ((natDegree_C_mul_le _ _).trans natDegree_X.le)

def densityRootPencil (x δ : K) : K[X] :=
  densityDeterminant 7 x + C δ*densityDeterminant 6 x

theorem densityRootPencil_eval (x δ s : K) :
    (densityRootPencil x δ).eval s = (actualPencil s δ).eval x := by
  simp only [densityRootPencil,eval_add,eval_mul,eval_C,densityDeterminant_eval,actualPencil_eval]

theorem densityRootPencil_degree (x δ : K) :
    (densityRootPencil x δ).natDegree ≤ 7 := by
  unfold densityRootPencil
  exact natDegree_add_le_of_le (densityDeterminant_degree _ _)
    ((natDegree_C_mul_le _ _).trans ((densityDeterminant_degree 6 x).trans (by decide : 6 ≤ 7)))

private theorem densityAffine_rat (j : ℕ) :
    (densityAffine (K := ℚ) j).map (Rat.castHom K) = densityAffine (K := K) j := by
  have bc (k : ℕ) : (Rat.castHom K) (threeInteriorBaseMoment (K := ℚ) k) =
      threeInteriorBaseMoment (K := K) k := by
    change ((threeInteriorBaseMoment (K := ℚ) k : ℚ) : K) =
      threeInteriorBaseMoment (K := K) k
    simp only [threeInteriorBaseMoment,Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_add,
      Rat.cast_natCast,Rat.cast_ofNat]
  simp only [densityAffine,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,
    Polynomial.map_sub, Polynomial.map_ofNat, _root_.map_mul, _root_.map_sub, map_ofNat, bc]

theorem densityDeterminant_rat (n : ℕ) (x : ℚ) :
    (densityDeterminant n x).map (Rat.castHom K) = densityDeterminant n (x : K) := by
  unfold densityDeterminant
  let f : ℚ →+* K := Rat.castHom K
  change Polynomial.mapRingHom f (Matrix.of (fun i j : Fin n =>
    densityAffine (i.val+j.val+1)-C x*densityAffine (i.val+j.val))).det = _
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change (densityAffine (K := ℚ) (i.val + j.val + 1) -
    C x * densityAffine (i.val + j.val)).map f =
      densityAffine (i.val + j.val + 1) - C (x : K) * densityAffine (i.val + j.val)
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, densityAffine_rat, f] <;> rfl

theorem densityRootPencil_rat (x δ : ℚ) :
    (densityRootPencil x δ).map (Rat.castHom K) = densityRootPencil (x : K) (δ : K) := by
  simp only [densityRootPencil,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,
    densityDeterminant_rat] <;> rfl

theorem determinantAt_rat (n : ℕ) (s x : ℚ) :
    determinantAt n (s : K) (x : K) = ((determinantAt n s x : ℚ) : K) := by
  have h := Polynomial.eval_map_apply (p := densityDeterminant n x) (f := Rat.castHom K) s
  rw [densityDeterminant_rat,densityDeterminant_eval,densityDeterminant_eval] at h
  exact h

theorem compactLower_rat (s : ℚ) :
    compactLower (s : K) = ((compactLower s : ℚ) : K) := by
  rw [compactLower_det,compactLower_det]
  rw [show (0:K) = ((0:ℚ):K) by simp]
  rw [determinantAt_rat,determinantAt_rat,Rat.cast_div,Rat.cast_neg]

theorem compactUpper_rat (s : ℚ) :
    compactUpper (s : K) = ((compactUpper s : ℚ) : K) := by
  rw [compactUpper_det,compactUpper_det]
  rw [show (1:K) = ((1:ℚ):K) by simp]
  rw [determinantAt_rat,determinantAt_rat,Rat.cast_div,Rat.cast_neg]

theorem defectBoxLow_rat (sl su jl : ℚ) :
    defectBoxLow (sl : K) (su : K) (jl : K) = ((defectBoxLow sl su jl : ℚ) : K) := by
  simp only [defectBoxLow,mix,compactLower_rat,compactUpper_rat,Rat.cast_add,Rat.cast_sub,
    Rat.cast_mul,Rat.cast_one]

theorem defectBoxHigh_rat (sl su ju : ℚ) :
    defectBoxHigh (sl : K) (su : K) (ju : K) = ((defectBoxHigh sl su ju : ℚ) : K) := by
  simp only [defectBoxHigh,mix,compactLower_rat,compactUpper_rat,Rat.cast_add,Rat.cast_sub,
    Rat.cast_mul,Rat.cast_one]

end
end RKCert.ReviewedNative.ThreeInteriorPencil
