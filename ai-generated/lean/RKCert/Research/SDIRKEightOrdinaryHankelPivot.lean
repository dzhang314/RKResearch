import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Ring

/-!
Weighted, masked moment matrices. The determinant identities do not assume
positive weights or an ordered field. Over a commutative ring they give a unit
matrix determinant when the masked weights and the individual differences are
units.
-/

open Matrix

namespace RKResearch.Certified.SDIRKEightOrdinaryHankelPivot

variable {R : Type*} [CommRing R] {n k : ℕ}

/-- Moment matrix for the finite weighted sites. -/
def weightedHankel (x w : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => ∑ a : Fin n, w a * x a ^ ((i : ℕ) + (j : ℕ))

theorem weightedHankel_factor (x w : Fin n → R) :
    weightedHankel x w = (vandermonde x)ᵀ * diagonal w * vandermonde x := by
  ext i j
  unfold weightedHankel
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.vandermonde_apply, pow_add]
  ring

theorem det_weightedHankel (x w : Fin n → R) :
    (weightedHankel x w).det = (vandermonde x).det ^ 2 * (∏ a : Fin n, w a) := by
  rw [weightedHankel_factor, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Matrix.det_diagonal]
  ring

theorem det_weightedHankel_ne_zero [IsDomain R] {x w : Fin n → R}
    (hx : Function.Injective x) (hw : ∀ a, w a ≠ 0) :
    (weightedHankel x w).det ≠ 0 := by
  rw [det_weightedHankel]
  exact mul_ne_zero (pow_ne_zero _ (Matrix.det_vandermonde_ne_zero_iff.mpr hx))
    (Finset.prod_ne_zero_iff.mpr fun a _ => hw a)

theorem det_weightedHankel_isUnit {x w : Fin n → R}
    (hx : ∀ a b, a ≠ b → IsUnit (x b - x a)) (hw : ∀ a, IsUnit (w a)) :
    IsUnit (weightedHankel x w).det := by
  rw [det_weightedHankel, Matrix.det_vandermonde]
  apply IsUnit.mul _ (IsUnit.prod_univ_iff.mpr hw)
  apply IsUnit.pow
  apply IsUnit.prod_univ_iff.mpr
  intro a
  apply IsUnit.prod_iff.mpr
  intro b hb
  exact hx a b (Finset.mem_Ioi.mp hb).ne

/-- The surviving weight after multiplying the test polynomial by the
product of the already known clock factors. -/
def maskedWeight (s : Fin k → R) (x w : Fin n → R) (a : Fin n) : R :=
  w a * ∏ j : Fin k, (x a - s j)

theorem det_maskedHankel_ne_zero [IsDomain R] {s : Fin k → R} {x w : Fin n → R}
    (hx : Function.Injective x) (hw : ∀ a, w a ≠ 0)
    (hs : ∀ a j, x a ≠ s j) :
    (weightedHankel x (maskedWeight s x w)).det ≠ 0 := by
  apply det_weightedHankel_ne_zero hx
  intro a
  exact mul_ne_zero (hw a)
    (Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr (hs a j))

theorem det_maskedHankel_isUnit {s : Fin k → R} {x w : Fin n → R}
    (hx : ∀ a b, a ≠ b → IsUnit (x b - x a)) (hw : ∀ a, IsUnit (w a))
    (hs : ∀ a j, IsUnit (x a - s j)) :
    IsUnit (weightedHankel x (maskedWeight s x w)).det := by
  apply det_weightedHankel_isUnit hx
  intro a
  exact (hw a).mul (IsUnit.prod_univ_iff.mpr (hs a))

/-- A moment matrix supplied by an abstract degree-truncated moment gate has
the same determinant, even when presented without its weighted sites. -/
theorem det_of_maskedMoment_isUnit {s : Fin k → R} {x w : Fin n → R}
    (M : ℕ → R)
    (hM : ∀ i j : Fin n, M ((i : ℕ) + (j : ℕ)) =
      ∑ a : Fin n, maskedWeight s x w a * x a ^ ((i : ℕ) + (j : ℕ)))
    (hx : ∀ a b, a ≠ b → IsUnit (x b - x a)) (hw : ∀ a, IsUnit (w a))
    (hs : ∀ a j, IsUnit (x a - s j)) :
    IsUnit (Matrix.of (fun i j : Fin n => M ((i : ℕ) + (j : ℕ)))).det := by
  have h : Matrix.of (fun i j : Fin n => M ((i : ℕ) + (j : ℕ))) =
      weightedHankel x (maskedWeight s x w) := by
    ext i j
    exact hM i j
  rw [h]
  exact det_maskedHankel_isUnit hx hw hs

/-- The masked Hankel equation has at most one solution under the explicit
ring unit guards. In particular this applies to the coefficient vector of the
monic polynomial on the as-yet unknown ordinary clocks. -/
theorem maskedHankel_injective {s : Fin k → R} {x w : Fin n → R}
    (hx : ∀ a b, a ≠ b → IsUnit (x b - x a)) (hw : ∀ a, IsUnit (w a))
    (hs : ∀ a j, IsUnit (x a - s j)) :
    Function.Injective (weightedHankel x (maskedWeight s x w)).mulVec :=
  mulVec_injective_of_det_mem_nonZeroDivisors (det_maskedHankel_isUnit hx hw hs).mem_nonZeroDivisors

/-- No division is needed to transport the Cramer equations to a coefficient
ring. The unit guard above justifies their subsequent inversion. -/
theorem cramer_of_maskedHankel_solution {s : Fin k → R} {x w : Fin n → R}
    {q target : Fin n → R}
    (h : weightedHankel x (maskedWeight s x w) *ᵥ q = target)
    (hx : ∀ a b, a ≠ b → IsUnit (x b - x a)) (hw : ∀ a, IsUnit (w a))
    (hs : ∀ a j, IsUnit (x a - s j)) :
    let H := weightedHankel x (maskedWeight s x w)
    cramer H target = H.det • q := by
  dsimp
  apply maskedHankel_injective hx hw hs
  rw [Matrix.mulVec_cramer, Matrix.mulVec_smul, h]

end RKResearch.Certified.SDIRKEightOrdinaryHankelPivot
