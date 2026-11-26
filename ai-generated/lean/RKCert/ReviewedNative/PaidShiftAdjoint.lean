module

public import RKCert.ReviewedNative.ProjectedMomentContext
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Logic.Function.Iterate

import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Paid polynomial adjoint of the shifted primitive

The checked unit moment moves a shifted primitive onto the test
polynomial with exactly one paid degree. Consecutive pure unary
steps can be moved together, without choosing a polynomial hull.
-/

namespace RKResearch.ContextCompletion.PaidShift

open Polynomial
open RKResearch.Certified.Graded (primitive primitive_natDegree_le)
open scoped Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The polynomial action of a strict row before restoring its diagonal. -/
def shift (γ : K) : K[X] →ₗ[K] K[X] :=
  primitive - γ • LinearMap.id

/-- The paid unit-moment adjoint, as an actual linear map. -/
def adjoint (γ : K) : K[X] →ₗ[K] K[X] :=
  (Algebra.linearMap K K[X]).comp unitMoment - primitive - γ • LinearMap.id

@[simp] theorem shift_apply (γ : K) (F : K[X]) :
    shift γ F = primitive F - γ • F := by
  simp only [shift, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]

@[simp] theorem adjoint_apply (γ : K) (W : K[X]) :
    adjoint γ W = C (unitMoment W) - primitive W - γ • W := by
  simp only [adjoint, LinearMap.sub_apply, LinearMap.comp_apply, Algebra.linearMap_apply,
    Polynomial.algebraMap_eq, LinearMap.smul_apply, LinearMap.id_apply]

theorem shift_natDegree_le (γ : K) (F : K[X]) :
    (shift γ F).natDegree ≤ F.natDegree + 1 := by
  rw [shift_apply]
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le (primitive_natDegree_le (le_refl F.natDegree))
      ((Polynomial.natDegree_smul_le γ F).trans (Nat.le_succ F.natDegree)))

theorem adjoint_natDegree_le (γ : K) (W : K[X]) :
    (adjoint γ W).natDegree ≤ W.natDegree + 1 := by
  rw [adjoint_apply]
  have hc : (C (unitMoment W)).natDegree ≤ W.natDegree + 1 := by
    simpa only [Polynomial.natDegree_C] using Nat.zero_le (W.natDegree + 1)
  have h₀ := (Polynomial.natDegree_sub_le (C (unitMoment W)) (primitive W)).trans
    (max_le hc (primitive_natDegree_le (le_refl W.natDegree)))
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le h₀ ((Polynomial.natDegree_smul_le γ W).trans (Nat.le_succ W.natDegree)))

/-- The same paid degree budget as the checked unshifted by-parts law. -/
theorem unitMoment_shift_byParts {p : ℕ} (units : PaidUnits K p) (γ : K)
    (W F : K[X]) (paid : W.natDegree + F.natDegree + 1 < p) :
    unitMoment (W * shift γ F) = unitMoment (adjoint γ W * F) := by
  calc
    unitMoment (W * shift γ F) =
        unitMoment (W * primitive F) - γ • unitMoment (W * F) := by
      simp only [shift_apply, mul_sub, mul_smul_comm, map_sub, map_smul]
    _ = unitMoment ((C (unitMoment W) - primitive W) * F) -
        γ • unitMoment (W * F) :=
      congrArg (fun a : K => a - γ • unitMoment (W * F))
        (unitMoment_byParts units W F paid)
    _ = unitMoment (adjoint γ W * F) := by
      simp only [adjoint_apply, sub_mul, smul_mul_assoc, map_sub, map_smul]

private theorem iterate_natDegree_le_of_step (P : K[X] → K[X])
    (step : ∀ F : K[X], (P F).natDegree ≤ F.natDegree + 1)
    (d : ℕ) (F : K[X]) :
    ((P^[d]) F).natDegree ≤ F.natDegree + d := by
  induction d with
  | zero => simp only [Function.iterate_zero_apply, Nat.add_zero, le_refl]
  | succ d ih =>
    rw [Function.iterate_succ_apply']
    exact (step _).trans (Nat.succ_le_succ ih)

theorem shift_iterate_natDegree_le (γ : K) (d : ℕ) (F : K[X]) :
    (((shift γ : K[X] → K[X])^[d]) F).natDegree ≤ F.natDegree + d :=
  iterate_natDegree_le_of_step (shift γ) (shift_natDegree_le γ) d F

theorem adjoint_iterate_natDegree_le (γ : K) (d : ℕ) (W : K[X]) :
    (((adjoint γ : K[X] → K[X])^[d]) W).natDegree ≤ W.natDegree + d :=
  iterate_natDegree_le_of_step (adjoint γ) (adjoint_natDegree_le γ) d W

/-- Move a string of d unary actions at cost d, with both sides charged. -/
theorem unitMoment_iterate_shift_byParts {p : ℕ} (units : PaidUnits K p) (γ : K)
    (d : ℕ) (W F : K[X]) (paid : W.natDegree + F.natDegree + d < p) :
    unitMoment ((((adjoint γ : K[X] → K[X])^[d]) W) * F) =
      unitMoment (W * (((shift γ : K[X] → K[X])^[d]) F)) := by
  induction d generalizing W F with
  | zero => simp only [Function.iterate_zero_apply]
  | succ d ih =>
    have testGrow := adjoint_natDegree_le γ W
    have inputGrow := shift_iterate_natDegree_le γ d F
    have payTest : (adjoint γ W).natDegree + F.natDegree + d < p := by omega
    have payInput :
        W.natDegree + (((shift γ : K[X] → K[X])^[d]) F).natDegree + 1 < p := by
      omega
    calc
      unitMoment ((((adjoint γ : K[X] → K[X])^[d+1]) W) * F) =
          unitMoment ((((adjoint γ : K[X] → K[X])^[d]) (adjoint γ W)) * F) := by
        rw [Function.iterate_succ_apply]
      _ = unitMoment (adjoint γ W * (((shift γ : K[X] → K[X])^[d]) F)) :=
        ih (adjoint γ W) F payTest
      _ = unitMoment (W * shift γ (((shift γ : K[X] → K[X])^[d]) F)) :=
        (unitMoment_shift_byParts units γ W _ payInput).symm
      _ = unitMoment (W * (((shift γ : K[X] → K[X])^[d+1]) F)) := by
        rw [Function.iterate_succ_apply']

/-- The test arriving at the end of a pure unary path. -/
def pureUnaryTest (γ : K) (d : ℕ) : K[X] :=
  ((adjoint γ : K[X] → K[X])^[d]) 1

@[simp] theorem pureUnaryTest_zero (γ : K) : pureUnaryTest γ 0 = 1 := rfl

theorem pureUnaryTest_succ (γ : K) (d : ℕ) :
    pureUnaryTest γ (d+1) = adjoint γ (pureUnaryTest γ d) := by
  simp only [pureUnaryTest, Function.iterate_succ_apply']

theorem pureUnaryTest_natDegree_le (γ : K) (d : ℕ) :
    (pureUnaryTest γ d).natDegree ≤ d := by
  simpa only [pureUnaryTest, Polynomial.natDegree_one, zero_add] using
    adjoint_iterate_natDegree_le γ d (1 : K[X])

theorem unitMoment_pureUnary_eq {p : ℕ} (units : PaidUnits K p) (γ : K)
    (d : ℕ) (F : K[X]) (paid : F.natDegree + d < p) :
    unitMoment (pureUnaryTest γ d * F) =
      unitMoment (((shift γ : K[X] → K[X])^[d]) F) := by
  have charge : (1 : K[X]).natDegree + F.natDegree + d < p := by
    simpa only [Polynomial.natDegree_one, zero_add] using paid
  simpa only [pureUnaryTest, one_mul] using
    unitMoment_iterate_shift_byParts units γ d (1 : K[X]) F charge

/-- A zero forward pure unary moment is also zero against its paid test.
The input may be any polynomial; this statement chooses no hull. -/
theorem unitMoment_pureUnary_cancel {p : ℕ} (units : PaidUnits K p) (γ : K)
    (d : ℕ) (F : K[X]) (paid : F.natDegree + d < p)
    (forward : unitMoment (((shift γ : K[X] → K[X])^[d]) F) = 0) :
    unitMoment (pureUnaryTest γ d * F) = 0 :=
  (unitMoment_pureUnary_eq units γ d F paid).trans forward

end

end RKResearch.ContextCompletion.PaidShift
