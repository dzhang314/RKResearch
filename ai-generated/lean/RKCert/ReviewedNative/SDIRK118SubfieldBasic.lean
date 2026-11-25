module

public import RKCert.ReviewedNative.SDIRK118ScalarExistence
public import Mathlib.FieldTheory.IntermediateField.Basic

import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Support

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.Subfield

open ClaimPin ScalarBindings ScalarExistence LiteralAssembly
open RKResearch.Certified.DiagonalTwin (contractMatrix)
open RKResearch.Certified.Graded (mergeCoefficient)
open scoped BigOperators Matrix

abbrev CoeffsIn (F : IntermediateField ℚ ℝ) (P : Polynomial ℝ) : Prop :=
  ∀ n : ℕ, P.coeff n ∈ F

abbrev VecIn {ι : Type*} (F : IntermediateField ℚ ℝ) (v : ι → ℝ) : Prop :=
  ∀ i, v i ∈ F

abbrev MatIn {ι κ : Type*} (F : IntermediateField ℚ ℝ) (A : Matrix ι κ ℝ) : Prop :=
  ∀ i j, A i j ∈ F

variable (F : IntermediateField ℚ ℝ)

theorem coeffs_one : CoeffsIn F (1 : Polynomial ℝ) := by
  intro n
  rw [Polynomial.coeff_one]
  split
  · exact F.one_mem
  · exact F.zero_mem

theorem coeffs_C {a : ℝ} (ha : a ∈ F) : CoeffsIn F (Polynomial.C a) := by
  intro n
  rw [Polynomial.coeff_C]
  split
  · exact ha
  · exact F.zero_mem

theorem coeffs_X : CoeffsIn F (Polynomial.X : Polynomial ℝ) := by
  intro n
  rw [Polynomial.coeff_X]
  split
  · exact F.one_mem
  · exact F.zero_mem

theorem coeffs_add {P Q : Polynomial ℝ} (hP : CoeffsIn F P) (hQ : CoeffsIn F Q) :
    CoeffsIn F (P + Q) := by
  intro n
  rw [Polynomial.coeff_add]
  exact F.add_mem (hP n) (hQ n)

theorem coeffs_sub {P Q : Polynomial ℝ} (hP : CoeffsIn F P) (hQ : CoeffsIn F Q) :
    CoeffsIn F (P - Q) := by
  intro n
  rw [Polynomial.coeff_sub]
  exact F.sub_mem (hP n) (hQ n)

theorem coeffs_mul {P Q : Polynomial ℝ} (hP : CoeffsIn F P) (hQ : CoeffsIn F Q) :
    CoeffsIn F (P * Q) := by
  intro n
  rw [Polynomial.coeff_mul]
  exact F.sum_mem fun a _ => F.mul_mem (hP a.1) (hQ a.2)

theorem coeffs_pow {P : Polynomial ℝ} (hP : CoeffsIn F P) (n : ℕ) : CoeffsIn F (P ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using coeffs_one F
  | succ n ih =>
    simpa only [pow_succ] using coeffs_mul F ih hP

theorem coeffs_smul {a : ℝ} {P : Polynomial ℝ} (ha : a ∈ F) (hP : CoeffsIn F P) :
    CoeffsIn F (a • P) := by
  intro n
  rw [Polynomial.coeff_smul, smul_eq_mul]
  exact F.mul_mem ha (hP n)

theorem coeffs_prod {ι : Type*} (S : Finset ι) (P : ι → Polynomial ℝ)
    (hP : ∀ i ∈ S, CoeffsIn F (P i)) : CoeffsIn F (∏ i ∈ S, P i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using coeffs_one F
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha]
    exact coeffs_mul F (hP a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hP i (Finset.mem_insert_of_mem hi)))

theorem evalAt_mem (M : MonomialBasis) (hm : standardPowers M)
    {x : ℝ} (hx : x ∈ F) {P : Polynomial ℝ} (hP : CoeffsIn F P) :
    evalAt M x P ∈ F := by
  have e : P = ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j • (Polynomial.X : Polynomial ℝ)^j := by
    simpa only [Polynomial.smul_eq_C_mul, Polynomial.C_mul_X_pow_eq_monomial]
      using P.as_sum_range
  rw [e]
  simp only [map_sum, map_smul, smul_eq_mul, eval_pow M hm]
  exact F.sum_mem fun j _ => F.mul_mem (hP j) (pow_mem hx j)

theorem primitive_coeffs (M : MonomialBasis) (hm : standardPowers M)
    {P : Polynomial ℝ} (hP : CoeffsIn F P) :
    CoeffsIn F (coefficientPrimitive M P) := by
  intro n
  cases n with
  | zero =>
    rw [primitive_coeff_zero_for_certificate M hm]
    exact F.zero_mem
  | succ n =>
    rw [primitive_coeff_succ_for_certificate M hm P n]
    exact F.div_mem (hP n) (F.natCast_mem (n+1))

theorem mean_mem (M : MonomialBasis) (hm : standardPowers M)
    {P : Polynomial ℝ} (hP : CoeffsIn F P) : mean M P ∈ F :=
  evalAt_mem F M hm F.one_mem (primitive_coeffs F M hm hP)

theorem avg_mem (M : MonomialBasis) (hm : standardPowers M)
    {z : ℝ} (hz : z ∈ F) {P : Polynomial ℝ} (hP : CoeffsIn F P) : avg M z P ∈ F :=
  F.div_mem (evalAt_mem F M hm hz (primitive_coeffs F M hm hP)) hz

theorem evalSites_mem (M : MonomialBasis) (hm : standardPowers M)
    {x : Fin 6 → ℝ} (hx : VecIn F x) {P : Polynomial ℝ} (hP : CoeffsIn F P) :
    VecIn F (evalSites M x P) :=
  fun i => evalAt_mem F M hm (hx i) hP

theorem vec_add {ι : Type*} {u v : ι → ℝ} (hu : VecIn F u) (hv : VecIn F v) :
    VecIn F (u + v) :=
  fun i => F.add_mem (hu i) (hv i)

theorem vec_sub {ι : Type*} {u v : ι → ℝ} (hu : VecIn F u) (hv : VecIn F v) :
    VecIn F (u - v) :=
  fun i => F.sub_mem (hu i) (hv i)

theorem vec_smul {ι : Type*} {a : ℝ} {v : ι → ℝ} (ha : a ∈ F) (hv : VecIn F v) :
    VecIn F (a • v) := by
  intro i
  simp only [Pi.smul_apply, smul_eq_mul]
  exact F.mul_mem ha (hv i)

theorem mat_smul {ι κ : Type*} {a : ℝ} {A : Matrix ι κ ℝ}
    (ha : a ∈ F) (hA : MatIn F A) : MatIn F (a • A) := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact F.mul_mem ha (hA i j)

theorem mulVec_mem {ι κ : Type*} [Fintype κ] {A : Matrix ι κ ℝ} {v : κ → ℝ}
    (hA : MatIn F A) (hv : VecIn F v) : VecIn F (A *ᵥ v) := by
  intro i
  change (∑ j : κ, A i j * v j) ∈ F
  exact F.sum_mem fun j _ => F.mul_mem (hA i j) (hv j)

theorem delta_mem {n : ℕ} (j : Fin n) : VecIn F (delta (K := ℝ) j) := by
  intro i
  unfold delta
  split
  · exact F.one_mem
  · exact F.zero_mem

theorem matrixOf_mem {m n : ℕ} {L : Vec n ℝ →ₗ[ℝ] Vec m ℝ}
    (hL : ∀ v, VecIn F v → VecIn F (L v)) : MatIn F (matrixOf L) :=
  fun i j => hL (delta j) (delta_mem F j) i

theorem submatrix_mem {ι κ ι' κ' : Type*} {A : Matrix ι κ ℝ}
    (hA : MatIn F A) (e : ι' → ι) (f : κ' → κ) :
    MatIn F (A.submatrix e f) :=
  fun i j => hA (e i) (f j)

theorem pull_mem {m n : ℕ} (e : Fin m → Fin n) {v : Vec n ℝ} (hv : VecIn F v) :
    VecIn F (pull e v) :=
  fun i => hv (e i)

theorem mergeCoefficient_mem {n : ℕ} (j : Fin (n+1)) (r : Fin n)
    {w : Fin (n+1) → ℝ} (hw : VecIn F w) : VecIn F (mergeCoefficient j r w) := by
  intro k
  unfold mergeCoefficient
  apply F.add_mem (hw (j.succAbove k))
  split
  · exact hw j
  · exact F.zero_mem

theorem contractMatrix_mem {n : ℕ} (j : Fin (n+1)) (r : Fin n)
    {A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ} (hA : MatIn F A) :
    MatIn F (contractMatrix j r A) :=
  fun i k => mergeCoefficient_mem F j r (hA (j.succAbove i)) k

end RKResearch.Certified.PaidDefectBridge.SDIRK118.Subfield
