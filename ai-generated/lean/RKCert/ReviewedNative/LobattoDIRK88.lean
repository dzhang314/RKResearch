module

public import RKCert.ReviewedNative.LobattoDIRK88Checks
public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import RKCert.ReviewedNative.LaguerreGauss76Real
public import RKCert.ReviewedNative.DIRKUniform

import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Sharp eight-stage, eighth-order ordinary DIRK

The archived Lobatto construction is realized over `ℚ(√21)` and replayed
using the native stage recurrence. In particular, the zero first row is
a genuine physical stage; the construction is not strict SDIRK. -/

namespace RKResearch.Certified.LobattoDIRK88

open RKResearch FiniteRootedTree CanonicalStageMemo
open RKCert.ReviewedNative.IntegerHornerCertificate
open RKCert.ReviewedNative.QuadraticHornerReplay
open scoped Matrix FiniteRootedTree

section Field

variable {K : Type*} [Field K]

noncomputable def A (s : K) : Matrix (Fin 8) (Fin 8) K :=
  ((stageDen:K)⁻¹) • numA s

noncomputable def b (s : K) : Fin 8 → K :=
  ((weightDen:K)⁻¹) • VecVal s rawB

private theorem rawA_zero_above {i j : Fin 8} (hij : i < j) :
    rawA i j = QExpr.zero := by
  change i.val < j.val at hij
  fin_cases i <;> fin_cases j <;> first | (norm_num at hij; done) | rfl

theorem lowerTriangular (s : K) : (A s).IsLowerTriangular := by
  intro i j hij
  change (stageDen:K)⁻¹ * (rawA i j).val 0 s = 0
  rw [rawA_zero_above (i := i) (j := j) hij, QExpr.val_zero, mul_zero]

theorem first_row_zero (s : K) (j : Fin 8) : A s 0 j = 0 := by
  change (stageDen:K)⁻¹ * (rawA 0 j).val 0 s = 0
  have hz : rawA 0 j = QExpr.zero := by fin_cases j <;> rfl
  rw [hz, QExpr.val_zero, mul_zero]

variable [CharZero K]

private theorem d_ne : (stageDen:K) ≠ 0 := Int.cast_ne_zero.mpr (by decide +kernel)
private theorem e_ne : (weightDen:K) ≠ 0 := Int.cast_ne_zero.mpr (by decide +kernel)

private theorem scale_A (s : K) : (stageDen:K) • A s = numA s := by
  rw [A, smul_smul, mul_inv_cancel₀ d_ne, one_smul]

private theorem scale_b (s : K) : (weightDen:K) • b s = VecVal s rawB := by
  rw [b, smul_smul, mul_inv_cancel₀ e_ne, one_smul]

theorem order_eight {s : K} (hs : s^2 = 21) : HasOrder 8 (A s) (b s) := by
  have hA : (numA s).map (RingHom.id K) = (RingHom.id K) (stageDen:K) • A s :=
    (scale_A s).symm
  have hb : (RingHom.id K) ∘ VecVal s rawB = (RingHom.id K) (weightDen:K) • b s :=
    (scale_b s).symm
  exact hasOrder_of_scaled_moments (RingHom.id K) hA hb
    (isUnit_iff_ne_zero.mpr d_ne) (isUnit_iff_ne_zero.mpr e_ne) (moments hs)

end Field

private def bush9 : Vec :=
  let v := deriv roots
  let v2 := point v v
  let v4 := point v2 v2
  point v4 v4

private theorem decoder_root {K : Type*} [CommRing K] {s : K} (hs : s^2 = 21) :
    VecVal s (deriv roots) = numA s *ᵥ 1 := by
  simpa only [roots_correct, decode, List.map_nil, List.prod_nil] using
    deriv_correct hs roots (by decide +kernel)

private theorem bush9_val {K : Type*} [CommRing K] {s : K} (hs : s^2 = 21) :
    Φ (bushyTree 9) (numA s) = VecVal s bush9 := by
  rw [Φ_bushyTree, show ((9:ℕ+):ℕ)-1 = 8 from rfl]
  simp only [bush9, point_val hs, decoder_root hs]
  ring

set_option maxHeartbeats 3500000 in
set_option maxRecDepth 10000 in
theorem ninth_bush_numerator {K : Type*} [CommRing K] {s : K} (hs : s^2 = 21) :
    (3920:K) * (9 * (VecVal s rawB ⬝ᵥ Φ (bushyTree 9) (numA s))) =
      3921 * ((weightDen:K)*(stageDen:K)^8) := by
  have hcheck : QExpr.eqMod innerMod 0
      ((sumWord bush9).scale (.atom [3920*9]))
      (QExpr.const (3921*weightDen*stageDen^8)) = true := by decide +kernel
  have h := QExpr.eqMod_sound hcheck (y := s) (inner_zero (K := K))
  rw [QExpr.val_scale, sumWord_val hs, QExpr.val_const, ← bush9_val hs] at h
  have hc : (Expr.atom [3920*9]).val (0:K) = (3920:K)*9 := by
    norm_num [Expr.val, coeval, horner]
  rw [hc] at h
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, mul_assoc] using h

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- The ninth bush has denominator-cleared excess `1/3920`. -/
theorem ninth_bush_scaled {s : K} (hs : s^2 = 21) :
    (3920:K) * (9 * (b s ⬝ᵥ Φ (bushyTree 9) (A s))) = 3921 := by
  let d : K := stageDen
  let e : K := weightDen
  have h := ninth_bush_numerator hs
  rw [← scale_A s, ← scale_b s, Φ_matrix_smul, order_bushyTree, smul_dotProduct,
    dotProduct_smul] at h
  change 3920 * (9 * (e * (d^8 * (b s ⬝ᵥ Φ (bushyTree 9) (A s))))) =
    3921*(e*d^8) at h
  have hn : e*d^8 ≠ 0 := mul_ne_zero e_ne (pow_ne_zero _ d_ne)
  apply mul_right_cancel₀ hn
  calc
    _ = 3920 * (9 * (e * (d^8 * (b s ⬝ᵥ Φ (bushyTree 9) (A s))))) := by ac_rfl
    _ = _ := h

theorem not_order_nine {s : K} (hs : s^2 = 21) : ¬ HasOrder 9 (A s) (b s) := by
  intro ho
  have hb : (9:K) * (b s ⬝ᵥ Φ (bushyTree 9) (A s)) = 1 := by
    simpa only [factorial_bushyTree, show ((9:ℕ+):ℕ) = 9 from rfl, Nat.cast_ofNat] using
      ho (bushyTree 9) (by rw [order_bushyTree]; decide)
  have h := ninth_bush_scaled hs
  rw [hb, mul_one] at h
  norm_num at h

theorem exists_exact_of_root {s : K} (hs : s^2 = 21) :
    ∃ (U : Matrix (Fin 8) (Fin 8) K) (w : Fin 8 → K),
      U.IsLowerTriangular ∧ (∀ j, U 0 j = 0) ∧ HasOrder 8 U w ∧ ¬ HasOrder 9 U w :=
  ⟨A s, b s, lowerTriangular s, first_row_zero s, order_eight hs, not_order_nine hs⟩

end Field

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

theorem exists_exact_realAlgebraic :
    ∃ (U : Matrix (Fin 8) (Fin 8) ℝₐ) (w : Fin 8 → ℝₐ),
      U.IsLowerTriangular ∧ (∀ j, U 0 j = 0) ∧ HasOrder 8 U w ∧ ¬ HasOrder 9 U w := by
  obtain ⟨s, -, hs⟩ := LaguerreGauss76.positive_algebraic_root 21 (by decide)
  exact exists_exact_of_root hs

theorem exists_exact_real :
    ∃ (U : Matrix (Fin 8) (Fin 8) ℝ) (w : Fin 8 → ℝ),
      U.IsLowerTriangular ∧ (∀ j, U 0 j = 0) ∧ HasOrder 8 U w ∧ ¬ HasOrder 9 U w := by
  obtain ⟨s, -, hs⟩ := LaguerreGauss76.positive_algebraic_root 21 (by decide)
  let f := algebraMap ℝₐ ℝ
  apply exists_exact_of_root (s := f s)
  have h := congrArg f hs
  rw [map_pow, map_natCast] at h
  exact h

end RKResearch.Certified.LobattoDIRK88

namespace RKResearch.Certified

theorem dirk_order_eight_isLeast_of_root {K : Type*} [Field K] [CharZero K]
    {s : K} (hs : s^2 = 21) :
    IsLeast {n : ℕ | ∃ (A : Matrix (Fin n) (Fin n) K) (b : Fin n → K),
      A.IsLowerTriangular ∧ HasOrder 8 A b} 8 := by
  obtain ⟨A,b,htr, -, ho, -⟩ := LobattoDIRK88.exists_exact_of_root hs
  refine ⟨⟨A,b,htr,ho⟩,?_⟩
  rintro n ⟨U,w,ht,h⟩
  exact h.dirk_order_eight_stages ht

theorem dirk_order_eight_isLeast_real :
    IsLeast {n : ℕ | ∃ (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ),
      A.IsLowerTriangular ∧ HasOrder 8 A b} 8 := by
  obtain ⟨A,b,htr, -, ho, -⟩ := LobattoDIRK88.exists_exact_real
  refine ⟨⟨A,b,htr,ho⟩,?_⟩
  rintro n ⟨U,w,ht,h⟩
  exact h.dirk_order_eight_stages ht

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

theorem dirk_order_eight_isLeast_realAlgebraic :
    IsLeast {n : ℕ | ∃ (A : Matrix (Fin n) (Fin n) ℝₐ) (b : Fin n → ℝₐ),
      A.IsLowerTriangular ∧ HasOrder 8 A b} 8 := by
  obtain ⟨A,b,htr, -, ho, -⟩ := LobattoDIRK88.exists_exact_realAlgebraic
  refine ⟨⟨A,b,htr,ho⟩,?_⟩
  rintro n ⟨U,w,ht,h⟩
  exact h.dirk_order_eight_stages ht

end RKResearch.Certified
