module

public import RKCert.ReviewedNative.GoodReductionFractionRoots
public import RKCert.ReviewedNative.CommonDiagonalTallObstruction
public import RKCert.ReviewedNative.NonsingularDIRKStageFloor
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Field.ZMod

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Rational strict SDIRK lower bounds at orders three and four

The modular obstruction is applied to the diagonal only, not to the
whole tableau. Lower bounds allow arbitrary rational weights and even
a zero common diagonal. The minima implications take witnesses as
input; this leaf does not construct a tableau. -/

namespace RKResearch.Certified

open Polynomial
open scoped Polynomial

/-- Diagonal equation for order at least three with at most two stages. -/
noncomputable def smallSDIRKDiagonal2 : ℤ[X] := C 6 * X^2 + C (-6)*X + C 1

/-- Diagonal equation for order at least four with at most three stages. -/
noncomputable def smallSDIRKDiagonal3 : ℤ[X] := C 24 * X^3 + C (-36)*X^2 + C 12*X + C (-1)

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private abbrev mod5 := Int.castRingHom (ZMod 5)

theorem smallSDIRKDiagonal2_mod5_no_root (x : ZMod 5) :
    ¬ (smallSDIRKDiagonal2.map (Int.castRingHom (ZMod 5))).IsRoot x := by
  change (smallSDIRKDiagonal2.map mod5).eval x ≠ 0
  rw [← Polynomial.eval₂_eq_eval_map]
  simp only [smallSDIRKDiagonal2,eval₂_add,eval₂_mul,eval₂_pow,eval₂_C,eval₂_X]
  fin_cases x <;> first | decide | norm_num [mod5]

theorem smallSDIRKDiagonal3_mod5_no_root (x : ZMod 5) :
    ¬ (smallSDIRKDiagonal3.map (Int.castRingHom (ZMod 5))).IsRoot x := by
  change (smallSDIRKDiagonal3.map mod5).eval x ≠ 0
  rw [← Polynomial.eval₂_eq_eval_map]
  simp only [smallSDIRKDiagonal3,eval₂_add,eval₂_mul,eval₂_pow,eval₂_C,eval₂_X]
  fin_cases x <;> first | decide | norm_num [mod5]

theorem smallSDIRKDiagonal2_no_rat_root (x : ℚ) : aeval x smallSDIRKDiagonal2 ≠ 0 := by
  have hl : mod5 smallSDIRKDiagonal2.leadingCoeff ≠ 0 := by
    rw [smallSDIRKDiagonal2,leadingCoeff_quadratic (by norm_num : (6:ℤ) ≠ 0)]
    decide
  exact no_fractionRoot_of_good_reduction mod5 _ hl smallSDIRKDiagonal2_mod5_no_root x

theorem smallSDIRKDiagonal3_no_rat_root (x : ℚ) : aeval x smallSDIRKDiagonal3 ≠ 0 := by
  have hl : mod5 smallSDIRKDiagonal3.leadingCoeff ≠ 0 := by
    rw [smallSDIRKDiagonal3,leadingCoeff_cubic (by norm_num : (24:ℤ) ≠ 0)]
    decide
  exact no_fractionRoot_of_good_reduction mod5 _ hl smallSDIRKDiagonal3_mod5_no_root x

end RKResearch.Certified

namespace RKResearch

open Certified Polynomial
open scoped Matrix BigOperators Polynomial

variable {s p : ℕ} {A : Matrix (Fin s) (Fin s) ℚ} {b : Fin s → ℚ} {γ : ℚ}

theorem HasOrder.rat_common_diagonal_order_three_stages (ho : HasOrder p A b)
    (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ) (hp : 3 ≤ p) :
    3 ≤ s := by
  by_contra! hs
  have h := ho.common_diagonal_tall_binomial_obstruction ha hc 2 (by omega) hp
  apply smallSDIRKDiagonal2_no_rat_root γ
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial] at h
  norm_num [smallSDIRKDiagonal2,Polynomial.aeval_def,eval₂_add,eval₂_mul,
    eval₂_pow,eval₂_C,eval₂_X]
  linear_combination (6:ℚ)*h

theorem HasOrder.rat_common_diagonal_order_four_stages (ho : HasOrder p A b)
    (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ) (hp : 4 ≤ p) :
    4 ≤ s := by
  by_contra! hs
  have h := ho.common_diagonal_tall_binomial_obstruction ha hc 3 (by omega) hp
  apply smallSDIRKDiagonal3_no_rat_root γ
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial] at h
  norm_num [smallSDIRKDiagonal3,Polynomial.aeval_def,eval₂_add,eval₂_mul,
    eval₂_pow,eval₂_C,eval₂_X]
  linear_combination (-24:ℚ)*h

end RKResearch

namespace RKResearch.Certified

/-- Native strict SDIRK existence at a given rational stage count. -/
def rationalStrictSDIRKStages (p : ℕ) : Set ℕ :=
  {s | ∃ (A : Matrix (Fin s) (Fin s) ℚ) (b : Fin s → ℚ) (γ : ℚ),
    A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder p A b}

/-- Exact-order version of the same stage count. -/
def rationalStrictSDIRKExactStages (p : ℕ) : Set ℕ :=
  {s | ∃ (A : Matrix (Fin s) (Fin s) ℚ) (b : Fin s → ℚ) (γ : ℚ),
    A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder p A b ∧ ¬ HasOrder (p+1) A b}

/-- Any matching three-stage order-three witness is automatically exact
by the rational order-four lower bound. Both notions of minimum follow. -/
theorem rational_strictSDIRK_three_minima_of_witness (hw : 3 ∈ rationalStrictSDIRKStages 3) :
    IsLeast (rationalStrictSDIRKStages 3) 3 ∧ IsLeast (rationalStrictSDIRKExactStages 3) 3 := by
  have hlo (s : ℕ) (h : s ∈ rationalStrictSDIRKStages 3) : 3 ≤ s := by
    obtain ⟨A,b,γ,ha,hγ,_,ho⟩ := h
    exact ho.rat_common_diagonal_order_three_stages ha hγ (by decide)
  refine ⟨⟨hw,fun _ h => hlo _ h⟩,⟨?_,?_⟩⟩
  · obtain ⟨A,b,γ,ha,hγ,hn,ho⟩ := hw
    refine ⟨A,b,γ,ha,hγ,hn,ho,?_⟩
    intro h
    have e := h.rat_common_diagonal_order_four_stages ha hγ (by decide)
    omega
  · rintro s ⟨A,b,γ,ha,hγ,hn,ho,_⟩
    exact hlo s ⟨A,b,γ,ha,hγ,hn,ho⟩

/-- Any matching four-stage order-four witness is automatically exact,
using the already reviewed common-diagonal order-five lower bound. -/
theorem rational_strictSDIRK_four_minima_of_witness (hw : 4 ∈ rationalStrictSDIRKStages 4) :
    IsLeast (rationalStrictSDIRKStages 4) 4 ∧ IsLeast (rationalStrictSDIRKExactStages 4) 4 := by
  have hlo (s : ℕ) (h : s ∈ rationalStrictSDIRKStages 4) : 4 ≤ s := by
    obtain ⟨A,b,γ,ha,hγ,_,ho⟩ := h
    exact ho.rat_common_diagonal_order_four_stages ha hγ (by decide)
  refine ⟨⟨hw,fun _ h => hlo _ h⟩,⟨?_,?_⟩⟩
  · obtain ⟨A,b,γ,ha,hγ,hn,ho⟩ := hw
    refine ⟨A,b,γ,ha,hγ,hn,ho,?_⟩
    intro h
    have e := h.common_diagonal_order_five_stages ha hγ
    omega
  · rintro s ⟨A,b,γ,ha,hγ,hn,ho,_⟩
    exact hlo s ⟨A,b,γ,ha,hγ,hn,ho⟩

end RKResearch.Certified
