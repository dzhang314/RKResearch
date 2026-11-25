module

public import RKCert.ReviewedNative.FiniteGaussianNodalLift
public import RKCert.ReviewedNative.PositiveIntervalGrid19
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Strict positivity on a paid finite integration grid

Draft. Positivity is assumed only at the actual grid nodes. The strict
step uses polynomial zero count, not sign continuity or a dense field.
-/
namespace RKCert.ReviewedNative.FiniteGaussianGridPositivity

open Polynomial
open RKCert.ReviewedNative.FiniteGaussianNodalLift
open RKCert.ReviewedNative.PositiveRule19
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem integral_pos_of_grid_nonneg {l r : K} (lr : l<r) (P : K[X])
    (nonzero : P ≠ 0) (degree : P.natDegree < 19)
    (nonneg : ∀ i : Fin 19, 0 ≤ P.eval (intervalPoint l r i)) :
    0 < integral l r P := by
  have live : ∃ i : Fin 19, P.eval (intervalPoint l r i) ≠ 0 := by
    by_contra all
    have zero (i : Fin 19) : P.eval (intervalPoint l r i) = 0 := by
      by_contra hz
      exact all ⟨i,hz⟩
    exact nonzero (eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
      (intervalPoint_strictMono lr).injective zero (by simpa using degree))
  obtain ⟨i,hi⟩ := live
  rw [interval_exact l r P degree.le]
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (intervalWeight_pos lr j).le (nonneg j)
  · exact ⟨i,Finset.mem_univ _,mul_pos (intervalWeight_pos lr i)
      (lt_of_le_of_ne (nonneg i) hi.symm)⟩

/-- An exact rule has positive masses if its cardinal-square tests are
paid by a strictly positive grid with enough distinct points. -/
theorem gaussian_mass_pos {ι : Type*} [DecidableEq ι]
    {l r : K} (lr : l<r) (W : K[X]) (Wnz : W ≠ 0)
    (nonneg : ∀ j : Fin 19, 0 ≤ W.eval (intervalPoint l r j))
    {t : Finset ι} {v : ι → K} {μ : ι → K} (nodes : Set.InjOn v t)
    (law : ExactRule (weighted (integral l r) W) t v μ (2*t.card-1))
    (room : W.natDegree + 2*(t.card-1) < 19)
    {i : ι} (hi : i ∈ t) :
    0 < μ i := by
  rw [mass_eq_cardinal_square nodes law hi,weighted_apply]
  let P := Lagrange.basis t v i
  change 0 < integral l r (W*P^2)
  have hP : P ≠ 0 := Lagrange.basis_ne_zero nodes hi
  have dP : P.natDegree ≤ t.card-1 := le_of_eq (Lagrange.natDegree_basis nodes hi)
  apply integral_pos_of_grid_nonneg lr _ (mul_ne_zero Wnz (pow_ne_zero _ hP))
    ((natDegree_mul_le_of_le (le_refl _) (natDegree_pow_le_of_le 2 dP)).trans_lt room)
  intro j
  simp only [eval_mul,eval_pow]
  exact mul_nonneg (nonneg j) (sq_nonneg _)

def unitWeight (K : Type*) [Field K] : K[X] := X*(1-X)

theorem unitWeight_degree : (unitWeight K).natDegree ≤ 2 := by
  unfold unitWeight
  apply natDegree_mul_le_of_le (m := 1) (n := 1)
  · simp
  · exact (natDegree_sub_le _ _).trans (by simp)

theorem unitWeight_nonzero : unitWeight K ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval ((1:K)/2)) h
  norm_num [unitWeight,eval_mul,eval_sub] at he

theorem unitWeight_eval_pos {x : K} (hl : 0<x) (hr : x<1) :
    0 < (unitWeight K).eval x := by
  simp only [unitWeight,eval_mul,eval_sub,eval_one,eval_X]
  exact mul_pos hl (sub_pos.mpr hr)

/-- The signed-profile residual need only be nonnegative on the fixed
unit grid. This is enough for all six augmented masses to be positive. -/
theorem unit_gaussian_mass_pos {ι : Type*} [DecidableEq ι]
    (B : K[X]) (Bne : B ≠ 0) (Bdeg : B.natDegree ≤ 2)
    (nonneg : ∀ j : Fin 19, 0 ≤ B.eval (intervalPoint (0:K) 1 j))
    {t : Finset ι} {v : ι → K} {μ : ι → K} (count : t.card = 6)
    (nodes : Set.InjOn v t)
    (law : ExactRule (weighted (integral 0 1) (unitWeight K*B)) t v μ 11)
    {i : ι} (hi : i ∈ t) :
    0 < μ i := by
  have lr : (0:K)<1 := zero_lt_one
  have deg : (unitWeight K*B).natDegree ≤ 4 :=
    natDegree_mul_le_of_le unitWeight_degree Bdeg
  have paid : ExactRule (weighted (integral 0 1) (unitWeight K*B)) t v μ (2*t.card-1) := by
    simpa only [count] using law
  apply gaussian_mass_pos lr (unitWeight K*B) (mul_ne_zero unitWeight_nonzero Bne)
    ?_ nodes paid (by omega) hi
  intro j
  have hx := intervalPoint_mem lr j
  simp only [eval_mul]
  exact mul_nonneg (unitWeight_eval_pos hx.1 hx.2).le (nonneg j)

end
end RKCert.ReviewedNative.FiniteGaussianGridPositivity
