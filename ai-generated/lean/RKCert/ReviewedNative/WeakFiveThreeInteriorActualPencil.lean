module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorCompactParameter
public import Mathlib.LinearAlgebra.Vandermonde

import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The actual compact determinant and its seven physical roots -/
namespace RKCert.ReviewedNative.ThreeInteriorPencil

open Polynomial Matrix RKCert.ReviewedNative.FiniteGaussianNodalLift
open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
open scoped Matrix Polynomial BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def pencilAt (n : ℕ) (s x : K) : Matrix (Fin n) (Fin n) K :=
  gramA n s-x • gramB n s

def determinantAt (n : ℕ) (s x : K) : K := (pencilAt n s x).det

/-- At fixed density, the trial-root variable is the polynomial variable. -/
def trialDeterminant (n : ℕ) (s : K) : K[X] :=
  (Matrix.of fun i j : Fin n => C (gramA n s i j)-C (gramB n s i j)*X).det

theorem trialDeterminant_eval (n : ℕ) (s x : K) :
    (trialDeterminant n s).eval x = determinantAt n s x := by
  unfold trialDeterminant determinantAt
  change Polynomial.evalRingHom x (Matrix.of (fun i j : Fin n =>
    C (gramA n s i j)-C (gramB n s i j)*X)).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  change (C (gramA n s i j) - C (gramB n s i j) * X).eval x = (pencilAt n s x) i j
  simp only [eval_sub, eval_mul, eval_C, eval_X,
    pencilAt, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [mul_comm x]

def actualPencil (s δ : K) : K[X] := trialDeterminant 7 s + C δ*trialDeterminant 6 s

theorem leading_pencilAt (n : ℕ) (s x : K) : leading (pencilAt (n+1) s x) = pencilAt n s x := rfl

theorem actualPencil_eval (s δ x : K) :
    (actualPencil s δ).eval x = determinantAt 7 s x + δ*determinantAt 6 s x := by
  simp only [actualPencil,eval_add,eval_mul,eval_C,trialDeterminant_eval]

theorem actualPencil_eval_det (s δ x : K) :
    (actualPencil s δ).eval x = (pencilAt 7 s x+border δ).det := by
  rw [actualPencil_eval,det_add_border,leading_pencilAt,determinantAt,determinantAt]

theorem compactLower_det (s : K) :
    compactLower s = -determinantAt 7 s 0 / determinantAt 6 s 0 := by
  simp only [compactLower,rayleighCost,leading_gramA,determinantAt,pencilAt,zero_smul,
    sub_zero,neg_div]

theorem compactUpper_det (s : K) :
    compactUpper s = -determinantAt 7 s 1 / determinantAt 6 s 1 := by
  have at_one (n : ℕ) : determinantAt n s 1 = (-gramCap n s).det := by
    rw [determinantAt,pencilAt,one_smul,gramCap_eq,neg_sub]
  rw [at_one 7,at_one 6,Matrix.det_neg,Matrix.det_neg]
  norm_num [compactUpper,rayleighCost,leading_gramCap,Fintype.card_fin]

theorem determinant6_unit_end_positive {s : K} (ss : s ∈ Set.Icc 0 1) :
    0 < determinantAt 6 s 0 ∧ 0 < determinantAt 6 s 1 := by
  letI : StarRing K := starRingOfComm
  letI : TrivialStar K := ⟨fun _ => rfl⟩
  have a : 0 < (gramA 6 s).det :=
    (momentGram_posDef 6 (by decide) ss natDegree_X.le x_unit_pos).det_pos
  have b : 0 < (gramCap 6 s).det :=
    (momentGram_posDef 6 (by decide) ss (unit_right_weight_degree (K := K)).le
      one_sub_x_unit_pos).det_pos
  constructor
  · simpa only [determinantAt,pencilAt,zero_smul,sub_zero] using a
  · have e : determinantAt 6 s 1 = (-gramCap 6 s).det := by
      rw [determinantAt,pencilAt,one_smul,gramCap_eq,neg_sub]
    rw [e,Matrix.det_neg]
    norm_num [Fintype.card_fin] <;> exact b

def atomicGram {n : ℕ} (β ω : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  (vandermonde β)ᵀ * Matrix.diagonal ω * vandermonde β

theorem atomicGram_apply {n : ℕ} (β ω : Fin n → K) (i j : Fin n) :
    atomicGram β ω i j = ∑ k : Fin n, ω k*(β k)^(i.val+j.val) := by
  rw [atomicGram,Matrix.mul_assoc,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.transpose_apply,Matrix.diagonal_mul,vandermonde_apply,pow_add]
  ring

theorem atomicGram_det {n : ℕ} (β ω : Fin n → K) :
    (atomicGram β ω).det = (vandermonde β).det^2*∏ k : Fin n,ω k := by
  rw [atomicGram,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,Matrix.det_diagonal,pow_two]
  ring

theorem gramB_eq_actual {s : K} {β ω : Fin 7 → K}
    (law : ExactRule (threeInteriorScaledMoment s) Finset.univ β ω 12) :
    gramB 7 s = atomicGram β ω := by
  ext i j
  rw [gramB_apply,atomicGram_apply]
  have d : i.val+j.val ≤ 12 := by have h := i.isLt; have k := j.isLt; omega
  simpa only [eval_pow,eval_X] using law (X^(i.val+j.val)) (by rwa [natDegree_X_pow])

theorem gramA_border_eq_actual {s : K} {β ω : Fin 7 → K}
    (law : ExactRule (threeInteriorScaledMoment s) Finset.univ β ω 12) :
    gramA 7 s+border (actualDefect s β ω) = atomicGram β (fun i => ω i*β i) := by
  ext i j
  rw [Matrix.add_apply,gramA_apply,atomicGram_apply]
  have shift : (∑ k : Fin 7,(ω k*β k)*(β k)^(i.val+j.val)) =
      ∑ k : Fin 7,ω k*(β k)^(i.val+j.val+1) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ']
    ring
  rw [shift,border,Matrix.single_apply]
  by_cases top : Fin.last 6 = i ∧ Fin.last 6 = j
  · obtain ⟨hi,hj⟩ := top
    subst i
    subst j
    simp only [Fin.val_last, true_and, ite_true]
    unfold actualDefect
    rw [indexedAtomicMoment_apply]
    simp only [eval_pow,eval_X]
    ring
  · have d : i.val+j.val+1 ≤ 12 := by
      have a := i.isLt
      have b := j.isLt
      by_contra! cut
      have hi : (Fin.last 6).val = i.val := by simp; omega
      have hj : (Fin.last 6).val = j.val := by simp; omega
      exact top ⟨Fin.ext hi,Fin.ext hj⟩
    rw [if_neg top,add_zero]
    simpa only [eval_pow,eval_X] using law (X^(i.val+j.val+1)) (by rwa [natDegree_X_pow])

theorem gramB_det_positive {s : K} {β ω : Fin 7 → K}
    (bi : Function.Injective β) (wp : ∀ i, 0 < ω i)
    (law : ExactRule (threeInteriorScaledMoment s) Finset.univ β ω 12) :
    0 < (gramB 7 s).det := by
  rw [gramB_eq_actual law,atomicGram_det]
  exact mul_pos (sq_pos_of_ne_zero (det_vandermonde_ne_zero_iff.mpr bi))
    (Finset.prod_pos (fun i _ => wp i))

theorem actualPencil_factor_eval {s : K} {β ω : Fin 7 → K}
    (law : ExactRule (threeInteriorScaledMoment s) Finset.univ β ω 12) (x : K) :
    (actualPencil s (actualDefect s β ω)).eval x =
      (gramB 7 s).det * ∏ k : Fin 7, (β k-x) := by
  have mat : pencilAt 7 s x+border (actualDefect s β ω) =
      atomicGram β (fun k => ω k*(β k-x)) := by
    calc
      pencilAt 7 s x+border (actualDefect s β ω) =
          (gramA 7 s+border (actualDefect s β ω))-x • gramB 7 s := by
        unfold pencilAt
        abel
      _ = _ := by
        rw [gramA_border_eq_actual law,gramB_eq_actual law]
        ext i j
        simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,atomicGram_apply,
          Finset.mul_sum,←Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
  rw [actualPencil_eval_det,mat,atomicGram_det,gramB_eq_actual law,atomicGram_det,
    Finset.prod_mul_distrib]
  ring

theorem actualPencil_factor {s : K} {β ω : Fin 7 → K}
    (law : ExactRule (threeInteriorScaledMoment s) Finset.univ β ω 12) :
    actualPencil s (actualDefect s β ω) =
      C (gramB 7 s).det * ∏ k : Fin 7, (C (β k)-X) := by
  apply Polynomial.funext
  intro x
  rw [actualPencil_factor_eval law]
  simp only [eval_mul,eval_C,eval_prod,eval_sub,eval_X]

theorem actualPencil_degree {s : K} {β ω : Fin 7 → K}
    (law : ExactRule (threeInteriorScaledMoment s) Finset.univ β ω 12) :
    (actualPencil s (actualDefect s β ω)).natDegree ≤ 7 := by
  rw [actualPencil_factor law]
  apply (natDegree_C_mul_le _ _).trans
  apply (natDegree_prod_le _ _).trans
  have h : (∑ k : Fin 7, (C (β k)-X : K[X]).natDegree) ≤ ∑ _ : Fin 7, (1:ℕ) :=
    Finset.sum_le_sum (fun k _ =>
      natDegree_sub_le_of_le ((natDegree_C (β k)).trans_le (Nat.zero_le 1)) natDegree_X.le)
  simpa using h

theorem actualPencil_roots {s : K} {β ω : Fin 7 → K}
    (law : ExactRule (threeInteriorScaledMoment s) Finset.univ β ω 12) :
    ∀ k, (actualPencil s (actualDefect s β ω)).IsRoot (β k) := by
  intro k
  change (actualPencil s (actualDefect s β ω)).eval (β k) = 0
  have zero : (∏ i : Fin 7, (β i-β k)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    exact sub_self (β k)
  rw [actualPencil_factor_eval law,zero,mul_zero]

theorem actualPencil_unit_end_signs {s : K} {β ω : Fin 7 → K}
    (bi : Function.Injective β) (inside : ∀ i, β i ∈ Set.Ioo 0 1) (wp : ∀ i, 0 < ω i)
    (law : ExactRule (threeInteriorScaledMoment s) Finset.univ β ω 12) :
    0 < (actualPencil s (actualDefect s β ω)).eval 0 ∧
      (actualPencil s (actualDefect s β ω)).eval 1 < 0 := by
  have gb := gramB_det_positive bi wp law
  constructor
  · rw [actualPencil_factor_eval law]
    simp only [sub_zero]
    exact mul_pos gb (Finset.prod_pos (fun i _ => (inside i).1))
  · rw [actualPencil_factor_eval law]
    have sh : (∏ i : Fin 7, (β i-1)) = -(∏ i : Fin 7, (1-β i)) := by
      have eq (i : Fin 7) : β i-1 = -(1-β i) := by ring
      simp only [eq,Finset.prod_neg,Finset.card_univ,Fintype.card_fin]
      have sign : (-1:K)^7 = -1 := by norm_num
      rw [sign,neg_one_mul]
    rw [sh]
    exact mul_neg_of_pos_of_neg gb
      (neg_lt_zero.mpr (Finset.prod_pos (fun i _ => sub_pos.mpr (inside i).2)))

end
end RKCert.ReviewedNative.ThreeInteriorPencil
