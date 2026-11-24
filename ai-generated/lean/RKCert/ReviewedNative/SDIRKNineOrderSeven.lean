module

public import RKCert.ReviewedNative.SDIRKNineReplayMoments
public import RKCert.ReviewedNative.SDIRKNineReplayRoots
public import RKCert.ReviewedNative.FiniteScaledOrderCheck

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public section

/-! # A strict nine-stage SDIRK of classical order at least seven

No numerical order, alternate tree type, or conversion of order predicates
is used. The two scalar units cancel the proved homogeneous numerator
identities for the full reviewed tree catalogue. -/

namespace RKResearch.Certified.SDIRKNineReplay

open RKCert.ReviewedNative.QuadraticHornerReplay

variable {K : Type*} [Field K] [CharZero K]

/-- The actual stage matrix. The physical common diagonal is `4 / x`. -/
noncomputable def A (x y : K) : Matrix (Fin 9) (Fin 9) K :=
  (((stageDen:K)*x)⁻¹) • numA x y

/-- The actual output weights. -/
noncomputable def b (x y : K) : Fin 9 → K :=
  ((weightDen:K)⁻¹) • VecVal x y rawB

private theorem stageDen_ne : (stageDen : K) ≠ 0 :=
  Int.cast_ne_zero.mpr (by decide +kernel)

private theorem weightDen_ne : (weightDen : K) ≠ 0 :=
  Int.cast_ne_zero.mpr (by decide +kernel)

private theorem rawA_zero_above {i j : Fin 9} (hij : i < j) :
    rawA i j = QExpr.zero := by
  change i.val < j.val at hij
  fin_cases i <;> fin_cases j <;> first | (norm_num at hij; done) | rfl

theorem lowerTriangular (x y : K) : (A x y).IsLowerTriangular := by
  intro i j hij
  change (((stageDen:K)*x)⁻¹) * (rawA i j).val x y = 0
  rw [rawA_zero_above (i := i) (j := j) hij, QExpr.val_zero, mul_zero]

theorem diagonal {x y : K} (hx : x ≠ 0) (i : Fin 9) : A x y i i = 4 / x := by
  have hd : (stageDen:K) ≠ 0 := stageDen_ne
  change (((stageDen:K)*x)⁻¹) * (rawA i i).val x y = 4 / x
  have hi : rawA i i = QExpr.const (4*stageDen) := by simp only [rawA, ↓reduceIte]
  rw [hi, QExpr.val_const, Int.cast_mul, Int.cast_ofNat]
  field_simp [hx, hd]

theorem order_seven {x y : K} (hx : x ≠ 0) (h : RootPair x y) :
    HasOrder 7 (A x y) (b x y) := by
  have hd : (stageDen : K) * x ≠ 0 := mul_ne_zero stageDen_ne hx
  have he : (weightDen:K) ≠ 0 := weightDen_ne
  have hA : (numA x y).map (RingHom.id K) = (RingHom.id K) ((stageDen:K)*x) • A x y := by
    change numA x y = ((stageDen:K)*x) • (((stageDen:K)*x)⁻¹ • numA x y)
    rw [smul_smul, mul_inv_cancel₀ hd, one_smul]
  have hb : (RingHom.id K) ∘ VecVal x y rawB = (RingHom.id K) (weightDen:K) • b x y := by
    change VecVal x y rawB = (weightDen:K) • ((weightDen:K)⁻¹ • VecVal x y rawB)
    rw [smul_smul, mul_inv_cancel₀ he, one_smul]
  exact hasOrder_of_scaled_moments (RingHom.id K) hA hb
    (isUnit_iff_ne_zero.mpr hd) (isUnit_iff_ne_zero.mpr he) (all_moments h)

theorem exists_of_rootPair {x y : K} (hx : x ≠ 0) (h : RootPair x y) :
    ∃ (A : Matrix (Fin 9) (Fin 9) K) (b : Fin 9 → K) (γ : K),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder 7 A b :=
  ⟨A x y, b x y, 4/x, lowerTriangular x y, diagonal hx, div_ne_zero (by norm_num) hx,
    order_seven hx h⟩

end RKResearch.Certified.SDIRKNineReplay

namespace RKResearch.Certified

theorem strictSDIRK_order_seven_nine_stages_real :
    ∃ (A : Matrix (Fin 9) (Fin 9) ℝ) (b : Fin 9 → ℝ) (γ : ℝ),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder 7 A b := by
  obtain ⟨x, y, hx, hy⟩ := SDIRKNineReplay.exists_real_rootPair
  exact SDIRKNineReplay.exists_of_rootPair hx hy

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

theorem strictSDIRK_order_seven_nine_stages_realAlgebraic :
    ∃ (A : Matrix (Fin 9) (Fin 9) ℝₐ) (b : Fin 9 → ℝₐ) (γ : ℝₐ),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder 7 A b := by
  obtain ⟨x, y, hx, hy⟩ := SDIRKNineReplay.exists_realAlgebraic_rootPair
  exact SDIRKNineReplay.exists_of_rootPair hx hy

end RKResearch.Certified
