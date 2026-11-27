module

public import RKCert.ReviewedNative.ERK10Stepanov
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! The positive nested roots select the authenticated real tableau.
Their quadratic and quartic polynomial relations put every coefficient
in the actual field of real algebraic numbers. -/

namespace RKResearch.Certified.ERK10Stepanov
open ERKNestedRadicalReplay Polynomial

theorem real_parameters : ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ Roots x y z := by
  let x := Real.sqrt 3
  let y := Real.sqrt 7
  have hpos : 0 < 147+42*y := add_pos_of_pos_of_nonneg (by norm_num)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  let z := Real.sqrt (147+42*y)
  exact ⟨x,y,z,Real.sqrt_pos.2 (by norm_num),Real.sqrt_pos.2 (by norm_num),Real.sqrt_pos.2 hpos,
    ⟨Real.mul_self_sqrt (by norm_num),Real.mul_self_sqrt (by norm_num),
      Real.mul_self_sqrt hpos.le⟩⟩

/-- The two nested radicals used by the published eight-coordinate file
have the asserted positive-root values under this normalization. -/
theorem source_radicals {x y z : ℝ} (h : Roots x y z) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    z/21 = Real.sqrt ((7+2*y)/21) ∧
      z*x*(y-2)/63 = Real.sqrt ((7-2*y)/21) := by
  have hy2 : 2 < y := by
    by_contra hn
    have e := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn)) (add_nonneg (show (0:ℝ)≤2 by norm_num) hy.le)
    nlinarith only [e,h.y_sq]
  have h1 : (z/21)*(z/21) = (7+2*y)/21 := by
    calc
      _ = (z*z)/441 := by ring
      _ = _ := by rw [h.z_sq]; ring
  have h2 : (z*x*(y-2)/63)*(z*x*(y-2)/63) = (7-2*y)/21 := by
    calc
      _ = (z*z)*(x*x)*((y-2)*(y-2))/3969 := by ring
      _ = (7-2*y)/21 + (126*y-63)*(y*y-7)/3969 := by rw [h.z_sq,h.x_sq]; ring
      _ = _ := by rw [h.y_sq]; ring
  constructor
  · rw [← h1, Real.sqrt_mul_self (div_nonneg hz.le (by norm_num))]
  · have hnonneg : 0 ≤ z*x*(y-2)/63 :=
      div_nonneg (mul_nonneg (mul_nonneg hz.le hx.le) (sub_nonneg.mpr hy2.le)) (by norm_num)
    rw [← h2, Real.sqrt_mul_self hnonneg]

private theorem quadratic_isAlgebraic (x : ℝ) (n : ℕ) (h : x*x = n) : IsAlgebraic ℚ x := by
  refine ⟨X^2 - C (n:ℚ), X_pow_sub_C_ne_zero (by decide) _, ?_⟩
  simp [pow_two,h]

private theorem outer_isAlgebraic {x y z : ℝ} (h : Roots x y z) : IsAlgebraic ℚ z := by
  let P : ℚ[X] := X^4 - C 294 * X^2 + C 9261
  have hcoef : P.coeff 4 = 1 := by
    norm_num [P,coeff_add,coeff_sub,coeff_C_mul,coeff_X_pow,coeff_C]
  have hv : z^4 - 294*z^2+9261 = 0 := by
    calc
      _ = (z*z-147)^2-12348 := by ring
      _ = 1764*(y*y-7) := by rw [h.z_sq]; ring
      _ = _ := by rw [h.y_sq]; ring
  refine ⟨P, ?_, ?_⟩
  · intro hp
    rw [hp, coeff_zero] at hcoef
    exact zero_ne_one hcoef
  · simpa [P] using hv

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

theorem realAlgebraic_parameters : ∃ x y z : ℝₐ,
    (0:ℝ) < (x:ℝ) ∧ (0:ℝ) < (y:ℝ) ∧ (0:ℝ) < (z:ℝ) ∧ Roots x y z := by
  obtain ⟨x,y,z,hx,hy,hz,h⟩ := real_parameters
  let xx : ℝₐ := ⟨x,mem_algebraicClosure_iff.mpr (quadratic_isAlgebraic x 3 (by simpa using h.x_sq))⟩
  let yy : ℝₐ := ⟨y,mem_algebraicClosure_iff.mpr (quadratic_isAlgebraic y 7 (by simpa using h.y_sq))⟩
  let zz : ℝₐ := ⟨z,mem_algebraicClosure_iff.mpr (outer_isAlgebraic h)⟩
  let f := algebraMap ℝₐ ℝ
  refine ⟨xx,yy,zz,hx,hy,hz,⟨f.injective ?_, f.injective ?_, f.injective ?_⟩⟩
  · simp only [map_mul,map_ofNat]
    change x*x = 3
    exact h.x_sq
  · simp only [map_mul,map_ofNat]
    change y*y = 7
    exact h.y_sq
  · simp only [map_mul,map_ofNat,map_add]
    change z*z = 147+42*y
    exact h.z_sq

private theorem denomUnit {K : Type*} [Field K] [CharZero K] : IsUnit (D:K) :=
  (Int.cast_ne_zero.mpr (show D ≠ 0 by decide +kernel)).isUnit

theorem exists_exact_real :
    ∃ (U : Matrix (Fin 15) (Fin 15) ℝ) (w : Fin 15 → ℝ),
      ERK U ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w := by
  obtain ⟨x,y,z,-,-,-,h⟩ := real_parameters
  exact exact_with_roots h denomUnit

theorem exists_exact_realAlgebraic :
    ∃ (U : Matrix (Fin 15) (Fin 15) ℝₐ) (w : Fin 15 → ℝₐ),
      ERK U ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w := by
  obtain ⟨x,y,z,-,-,-,h⟩ := realAlgebraic_parameters
  exact exact_with_roots h denomUnit

end RKResearch.Certified.ERK10Stepanov

#print axioms RKResearch.Certified.ERK10Stepanov.exists_exact_real
#print axioms RKResearch.Certified.ERK10Stepanov.exists_exact_realAlgebraic
