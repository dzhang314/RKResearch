module

public import RKCert.ReviewedNative.LobattoDIRK109Checks
public import RKCert.ReviewedNative.LobattoDIRK109Roots
public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import RKCert.ReviewedNative.DIRKUniform

import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Sharp ten-stage lower triangular DIRK of classical order nine

The witnessed upper bound uses the exact archived Lobatto tableau.
Its first row is literally zero. Native sharpness uses the checked
uniform DIRK lower bound specialized to order nine. -/

namespace RKResearch.Certified.LobattoDIRK109

open RKResearch FiniteRootedTree
open RKCert.ReviewedNative.IntegerHornerCertificate
open RKCert.ReviewedNative.QuadraticHornerReplay
open scoped Matrix FiniteRootedTree

section Field

variable {K : Type*} [Field K]

noncomputable def A (x y : K) : Matrix (Fin 10) (Fin 10) K :=
  ((stageDen:K)⁻¹) • numA x y

noncomputable def b (x y : K) : Fin 10 → K :=
  ((weightDen:K)⁻¹) • VecVal x y rawB

private theorem rawA_zero_above {i j : Fin 10} (hij : i < j) :
    rawA i j = QExpr.zero := by
  change i.val < j.val at hij
  fin_cases i <;> fin_cases j <;> first | (norm_num at hij; done) | rfl

theorem lowerTriangular (x y : K) : (A x y).IsLowerTriangular := by
  intro i j hij
  change (stageDen:K)⁻¹ * (rawA i j).val x y = 0
  rw [rawA_zero_above (i := i) (j := j) hij, QExpr.val_zero, mul_zero]

theorem first_row_zero (x y : K) (j : Fin 10) : A x y 0 j = 0 := by
  change (stageDen:K)⁻¹ * (rawA 0 j).val x y = 0
  have hz : rawA 0 j = QExpr.zero := by fin_cases j <;> rfl
  rw [hz, QExpr.val_zero, mul_zero]

variable [CharZero K]

theorem d_ne : (stageDen:K) ≠ 0 := Int.cast_ne_zero.mpr (by decide +kernel)
theorem e_ne : (weightDen:K) ≠ 0 := Int.cast_ne_zero.mpr (by decide +kernel)

theorem scale_A (x y : K) : (stageDen:K) • A x y = numA x y := by
  rw [A, smul_smul, mul_inv_cancel₀ d_ne, one_smul]

theorem scale_b (x y : K) : (weightDen:K) • b x y = VecVal x y rawB := by
  rw [b, smul_smul, mul_inv_cancel₀ e_ne, one_smul]

theorem order_nine {x y : K} (hx : coeval innerMod x = 0) (hy : y^2 = 7) :
    HasOrder 9 (A x y) (b x y) := by
  have hA : (numA x y).map (RingHom.id K) = (RingHom.id K) (stageDen:K) • A x y :=
    (scale_A x y).symm
  have hb : (RingHom.id K) ∘ VecVal x y rawB = (RingHom.id K) (weightDen:K) • b x y :=
    (scale_b x y).symm
  exact hasOrder_of_scaled_moments (RingHom.id K) hA hb
    (isUnit_iff_ne_zero.mpr d_ne) (isUnit_iff_ne_zero.mpr e_ne) (moments hx hy)

theorem exists_order_of_roots {x y : K} (hx : coeval innerMod x = 0) (hy : y^2 = 7) :
    ∃ (U : Matrix (Fin 10) (Fin 10) K) (w : Fin 10 → K),
      U.IsLowerTriangular ∧ (∀ j, U 0 j = 0) ∧ HasOrder 9 U w :=
  ⟨A x y, b x y, lowerTriangular x y, first_row_zero x y, order_nine hx hy⟩

end Field

theorem exists_order_real :
    ∃ (U : Matrix (Fin 10) (Fin 10) ℝ) (w : Fin 10 → ℝ),
      U.IsLowerTriangular ∧ (∀ j, U 0 j = 0) ∧ HasOrder 9 U w := by
  obtain ⟨x, y, -, -, hx, hy⟩ := exists_real_parameters
  exact exists_order_of_roots hx hy

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

theorem exists_order_realAlgebraic :
    ∃ (U : Matrix (Fin 10) (Fin 10) ℝₐ) (w : Fin 10 → ℝₐ),
      U.IsLowerTriangular ∧ (∀ j, U 0 j = 0) ∧ HasOrder 9 U w := by
  obtain ⟨x, y, -, -, hx, hy⟩ := exists_realAlgebraic_parameters
  exact exists_order_of_roots hx hy

end RKResearch.Certified.LobattoDIRK109

namespace RKResearch.Certified

open RKCert.ReviewedNative.IntegerHornerCertificate

private theorem dirk_order_nine_isLeast_of_exists {K : Type*} [CommRing K] [Nontrivial K]
    (h : ∃ (A : Matrix (Fin 10) (Fin 10) K) (b : Fin 10 → K),
      A.IsLowerTriangular ∧ (∀ j, A 0 j = 0) ∧ HasOrder 9 A b) :
    IsLeast {n : ℕ | ∃ (A : Matrix (Fin n) (Fin n) K) (b : Fin n → K),
      A.IsLowerTriangular ∧ HasOrder 9 A b} 10 := by
  obtain ⟨A,b,htr, -, ho⟩ := h
  refine ⟨⟨A,b,htr,ho⟩,?_⟩
  rintro n ⟨U,w,ht,h⟩
  exact h.dirk_uniform_stages ht (by decide)

theorem dirk_order_nine_isLeast_of_roots {K : Type*} [Field K] [CharZero K]
    {x y : K} (hx : coeval LobattoDIRK109.innerMod x = 0) (hy : y^2 = 7) :
    IsLeast {n : ℕ | ∃ (A : Matrix (Fin n) (Fin n) K) (b : Fin n → K),
      A.IsLowerTriangular ∧ HasOrder 9 A b} 10 :=
  dirk_order_nine_isLeast_of_exists (LobattoDIRK109.exists_order_of_roots hx hy)

theorem dirk_order_nine_isLeast_real :
    IsLeast {n : ℕ | ∃ (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ),
      A.IsLowerTriangular ∧ HasOrder 9 A b} 10 :=
  dirk_order_nine_isLeast_of_exists LobattoDIRK109.exists_order_real

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

theorem dirk_order_nine_isLeast_realAlgebraic :
    IsLeast {n : ℕ | ∃ (A : Matrix (Fin n) (Fin n) ℝₐ) (b : Fin n → ℝₐ),
      A.IsLowerTriangular ∧ HasOrder 9 A b} 10 :=
  dirk_order_nine_isLeast_of_exists LobattoDIRK109.exists_order_realAlgebraic

end RKResearch.Certified
