module

public import RKCert.ReviewedNative.DIRKPairedOriginResidue
public import RKCert.ReviewedNative.GradedDefects
public import RKCert.ReviewedNative.GradedPrimitives
public import RKCert.ReviewedNative.OneOffDebut

import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Actual centered grade payment for the paired origin residue

The raw paired body is separate. No normalization unit is needed for
its actual grade membership. Normalized display identities take only
the field units they use. A one-row paid probe needs separately earned
annihilation on the actual centered grade, not a presumed equality of
that grade with a polynomial band. -/
namespace RKResearch.Certified.Graded.PairedOrigin

open RKResearch Polynomial OneOff
open scoped Classical Matrix

variable {K : Type*} [Field K] {s : ℕ}

noncomputable def originResidual (A : Matrix (Fin s) (Fin s) K) (γ : K) : Fin s → K :=
  stageResidual A (originPrimitive γ)

noncomputable def nextResidual (A : Matrix (Fin s) (Fin s) K) (γ : K) : Fin s → K :=
  stageResidual A (nextPrimitive γ)

/-- A caller can choose its scalar transparently. This is not a
claim that a fixed scalar realizes the exact joint mask for all A. -/
noncomputable def pairedResidual (A : Matrix (Fin s) (Fin s) K)
    (γ lam : K) : Fin s → K :=
  originResidual A γ + lam • nextResidual A γ

private theorem eval_prim_expand (γ x : K) :
    (originPrimitive γ).eval x = x^3 - (2*γ)*x^2 + γ^2*x := by
  rw [eval_originPrimitive]
  ring

private theorem eval_next_expand (γ x : K) :
    (nextPrimitive γ).eval x = x^4 - (2*γ)*x^3 + γ^2*x^2 := by
  rw [eval_nextPrimitive, eval_prim_expand]
  ring

private theorem deriv_prim_expand (γ x : K) :
    (originPrimitive γ).derivative.eval x = 3*x^2 - (4*γ)*x + γ^2 := by
  rw [eval_derivative_originPrimitive]
  ring

private theorem deriv_next_expand (γ x : K) :
    (nextPrimitive γ).derivative.eval x = 4*x^3 - (6*γ)*x^2 + (2*γ^2)*x := by
  rw [eval_derivative_nextPrimitive, eval_prim_expand, deriv_prim_expand]
  ring

private theorem native_monomial_apply (A : Matrix (Fin s) (Fin s) K) (j : ℕ) (i : Fin s) :
    monomialStageDefect A j i =
      ((j+1:ℕ):K) * mat A ((nodes A)^j) i - (nodes A i)^(j+1) :=
  rfl

private theorem deriv_prim_col (A : Matrix (Fin s) (Fin s) K) (γ : K) :
    (fun i => (originPrimitive γ).derivative.eval (nodes A i)) =
      (3:K) • (nodes A)^2 - (4*γ) • nodes A + γ^2 • (1 : Fin s → K) := by
  funext i
  simp only [deriv_prim_expand, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.smul_apply,
    smul_eq_mul, Pi.one_apply, mul_one]

private theorem deriv_next_col (A : Matrix (Fin s) (Fin s) K) (γ : K) :
    (fun i => (nextPrimitive γ).derivative.eval (nodes A i)) =
      (4:K) • (nodes A)^3 - (6*γ) • (nodes A)^2 + (2*γ^2) • nodes A := by
  funext i
  simp only [deriv_next_expand, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.smul_apply,
    smul_eq_mul]

/-- The true grade-three residual in the denominator-cleared local API. -/
theorem originResidual_native (A : Matrix (Fin s) (Fin s) K) (γ : K) :
    originResidual A γ = monomialStageDefect A 2 - (2*γ) • monomialStageDefect A 1 := by
  funext i
  have rowOne : mat A (1 : Fin s → K) i = nodes A i := rfl
  simp only [originResidual, stageResidual, deriv_prim_col, map_add, map_sub, map_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rowOne, eval_prim_expand,
    native_monomial_apply, pow_one]
  norm_num <;> ring

/-- The true grade-four residual in the denominator-cleared local API. -/
theorem nextResidual_native (A : Matrix (Fin s) (Fin s) K) (γ : K) :
    nextResidual A γ = monomialStageDefect A 3 - (2*γ) • monomialStageDefect A 2 +
      γ^2 • monomialStageDefect A 1 := by
  funext i
  simp only [nextResidual, stageResidual, deriv_next_col, map_add, map_sub, map_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eval_next_expand,
    native_monomial_apply, pow_one]
  norm_num <;> ring

private theorem cleared_eq_scaled_mDef (A : Matrix (Fin s) (Fin s) K) (j : ℕ)
    (hn : ((j+1:ℕ):K) ≠ 0) :
    monomialStageDefect A j = ((j+1:ℕ):K) • mDef A j := by
  rw [mDef, smul_smul, mul_inv_cancel₀ hn, one_smul]

/-- The normalized grade-three display needs only the cast of 3:
the degree-one term's coefficient already vanishes in characteristic two. -/
theorem originResidual_normalized (A : Matrix (Fin s) (Fin s) K) (γ : K)
    (three : (3:K) ≠ 0) :
    originResidual A γ = (3:K) • mDef A 2 - (4*γ) • mDef A 1 := by
  have e3 : monomialStageDefect A 2 = (3:K) • mDef A 2 := by
    simpa using cleared_eq_scaled_mDef A 2 (by simpa using three)
  rw [originResidual_native, e3]
  by_cases h2 : (2:K) = 0
  · have h4 : (4:K) = 0 := by
      calc
        (4:K) = 2 * 2 := by ring
        _ = 0 := by rw [h2, zero_mul]
    simp only [h2, h4, zero_mul, zero_smul, sub_zero]
  · have e2 : monomialStageDefect A 1 = (2:K) • mDef A 1 := by
      simpa using cleared_eq_scaled_mDef A 1 (by simpa using h2)
    have hs : (2*γ)*(2:K) = 4*γ := by ring
    simp only [e2, smul_smul, hs]

/-- The normalized grade-four display needs the casts of 2 and 3.
The cast of 4 is the square of the cast of 2. -/
theorem nextResidual_normalized (A : Matrix (Fin s) (Fin s) K) (γ : K)
    (two : (2:K) ≠ 0) (three : (3:K) ≠ 0) :
    nextResidual A γ = (4:K) • mDef A 3 - (6*γ) • mDef A 2 +
      (2*γ^2) • mDef A 1 := by
  have four : (4:K) ≠ 0 := by
    have eq : (4:K) = 2 * 2 := by ring
    rw [eq]
    exact mul_ne_zero two two
  have e2 : monomialStageDefect A 1 = (2:K) • mDef A 1 := by
    simpa using cleared_eq_scaled_mDef A 1 (by simpa using two)
  have e3 : monomialStageDefect A 2 = (3:K) • mDef A 2 := by
    simpa using cleared_eq_scaled_mDef A 2 (by simpa using three)
  have e4 : monomialStageDefect A 3 = (4:K) • mDef A 3 := by
    simpa using cleared_eq_scaled_mDef A 3 (by simpa using four)
  have hs : (2*γ)*(3:K) = 6*γ := by ring
  have ht : γ^2*(2:K) = 2*γ^2 := by ring
  simp only [nextResidual_native, e2, e3, e4, smul_smul, hs, ht]

theorem originResidual_mem_grade (A : Matrix (Fin s) (Fin s) K) (γ : K) :
    originResidual A γ ∈ zeroSpace A 3 := by
  rw [originResidual_native]
  exact (zeroSpace A 3).sub_mem (monomialStageDefect_mem A 2)
    ((zeroSpace A 3).smul_mem _ (zeroSpace_mono A (by decide : 2 ≤ 3)
      (monomialStageDefect_mem A 1)))

theorem nextResidual_mem_grade (A : Matrix (Fin s) (Fin s) K) (γ : K) :
    nextResidual A γ ∈ zeroSpace A 4 := by
  rw [nextResidual_native]
  exact (zeroSpace A 4).add_mem
    ((zeroSpace A 4).sub_mem (monomialStageDefect_mem A 3)
      ((zeroSpace A 4).smul_mem _ (zeroSpace_mono A (by decide : 3 ≤ 4)
        (monomialStageDefect_mem A 2))))
    ((zeroSpace A 4).smul_mem _ (zeroSpace_mono A (by decide : 2 ≤ 4)
      (monomialStageDefect_mem A 1)))

section Origin

variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K}

/-- The actual graded zero space restricted to columns zero at the
physical origin, not the whole zero space or a presumed tight band. -/
def centeredZeroSpace (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (j : ℕ) :
    Submodule K (Fin (s+1) → K) :=
  zeroSpace A j ⊓ (LinearMap.proj (0 : Fin (s+1)) : (Fin (s+1) → K) →ₗ[K] K).ker

theorem mem_centeredZeroSpace {j : ℕ} {v : Fin (s+1) → K} :
    v ∈ centeredZeroSpace A j ↔ v ∈ zeroSpace A j ∧ v 0 = 0 := by
  simp only [centeredZeroSpace, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply]

theorem pairedResidual_mem_centered (γ lam : K)
    (upper : ∀ i, (0 : Fin (s+1)) < i → A 0 i = 0) (diagonal : A 0 0 = γ) :
    pairedResidual A γ lam ∈ centeredZeroSpace A 4 := by
  refine mem_centeredZeroSpace.mpr ⟨?_,?_⟩
  · exact (zeroSpace A 4).add_mem
      (zeroSpace_mono A (by decide : 3 ≤ 4) (originResidual_mem_grade A γ))
      ((zeroSpace A 4).smul_mem _ (nextResidual_mem_grade A γ))
  · obtain ⟨hg,hh⟩ := paired_actual_origin_clean A upper diagonal
    simp only [pairedResidual, originResidual, nextResidual, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, hg, hh, mul_zero, add_zero]

private theorem clockPower_mem {r : ℕ} {v : Fin (s+1) → K}
    (hv : v ∈ zeroSpace A r) (n : ℕ) :
    (fun i => v i * (nodes A i)^n) ∈ zeroSpace A (r+n) := by
  induction n with
  | zero => simpa only [pow_zero, mul_one, Nat.add_zero] using hv
  | succ n ih =>
    have h : diag (nodes A) (fun i => v i * (nodes A i)^n) ∈ zeroSpace A (r+n+1) :=
      diag_zeroSpace A (r+n) ih
    have eq : diag (nodes A) (fun i => v i * (nodes A i)^n) =
        (fun i => v i * (nodes A i)^(n+1)) := by
      funext i
      rw [diag_apply, pow_succ]
      ring
    rw [eq] at h
    exact h

/-- Clock multiplication is purely graded and does not use any cast units. -/
theorem defectPolynomial_mem_centered {r d : ℕ} {v : Fin (s+1) → K}
    (seed : v ∈ centeredZeroSpace A r) {P : K[X]} (degree : P.natDegree ≤ d) :
    diag v (evalNodes A P) ∈ centeredZeroSpace A (r+d) := by
  obtain ⟨hv,h0⟩ := mem_centeredZeroSpace.mp seed
  refine mem_centeredZeroSpace.mpr ⟨?_,?_⟩
  · rw [P.as_sum_range' (d+1) (by omega), map_sum, map_sum]
    apply (zeroSpace A (r+d)).sum_mem
    intro n hn
    rw [evalNodes_monomial, normTree_clockTree, map_smul]
    apply (zeroSpace A (r+d)).smul_mem
    have le : n ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    exact zeroSpace_mono A (Nat.add_le_add_left le r) (clockPower_mem hv n)
  · simp only [diag_apply, h0, zero_mul]

private theorem mat_at_origin
    (upper : ∀ i, (0 : Fin (s+1)) < i → A 0 i = 0) (v : Fin (s+1) → K) :
    mat A v 0 = A 0 0 * v 0 := by
  rw [mat_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_single 0
  · intro i _ ne
    rw [upper i (lt_of_le_of_ne (Fin.zero_le i) (fun e=>ne e.symm)), zero_mul]
  · intro no
    exact (no (Finset.mem_univ _)).elim

/-- The ordinary one-grade A-lift preserves the actual origin kernel.
Only the reviewed generator-order units are charged to this lift. -/
theorem mat_mem_centered_of_unit {j : ℕ} {v : Fin (s+1) → K}
    (upper : ∀ i, (0 : Fin (s+1)) < i → A 0 i = 0)
    (units : ∀ t : FiniteRootedTree, (t.order:ℕ) ≤ j+1 → IsUnit (((t.order:ℕ):K)))
    (seed : v ∈ centeredZeroSpace A j) :
    mat A v ∈ centeredZeroSpace A (j+1) := by
  obtain ⟨hv,h0⟩ := mem_centeredZeroSpace.mp seed
  refine mem_centeredZeroSpace.mpr ⟨mat_zeroSpace_of_unit A j units hv,?_⟩
  rw [mat_at_origin upper, h0, mul_zero]

/-- Actual incoming probes of the paired residue are paid at a recipient
that annihilates the displayed centered grade. The latter condition is
an earned premise; no rank or band saturation is assumed. -/
theorem paid_pairedResidue_of_centered_annihilation
    {γ lam : K} {k : Fin (s+1)} {d : ℕ}
    (upper : ∀ i, (0 : Fin (s+1)) < i → A 0 i = 0) (diagonal : A 0 0 = γ)
    (units : ∀ t : FiniteRootedTree, (t.order:ℕ) ≤ 4+d+1 → IsUnit (((t.order:ℕ):K)))
    (kill : ∀ v ∈ centeredZeroSpace A (4+d+1), v k = 0) :
    ∀ P : K[X], P.natDegree ≤ d →
      mat A (diag (pairedResidual A γ lam) (evalNodes A P)) k = 0 := by
  intro P hP
  exact kill _ (mat_mem_centered_of_unit upper units
    (defectPolynomial_mem_centered (pairedResidual_mem_centered γ lam upper diagonal) hP))

end Origin
end RKResearch.Certified.Graded.PairedOrigin
