module

public import RKCert.ReviewedNative.CrossedGaussianSignedAdapter
import Mathlib.Algebra.Order.Field.Basic
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Scalar transport of a signed nodal law from its paid monomials

Draft. This transfer is algebraic; it moves the moment equations, never a
base-field sign census. For positivity one carries only the indicated
finite mapped grids.
-/
namespace RKCert.ReviewedNative.FiniteGaussianNodalLift

open Polynomial
open scoped BigOperators

noncomputable section
variable {K L : Type*} [Field K] [Field L]

theorem exactRule_of_monomials {ι : Type*} {J : K[X] →ₗ[K] K}
    {s : Finset ι} {v μ : ι → K} {d : ℕ}
    (mon : ∀ n : ℕ, n≤d → J (X^n) = ∑ i ∈ s, μ i*(v i)^n) :
    ExactRule J s v μ d := by
  let A : K[X] →ₗ[K] K := ∑ i ∈ s, μ i • Polynomial.leval (v i)
  have app (P : K[X]) : A P = ∑ i ∈ s, μ i*P.eval (v i) := by
    simp [A,LinearMap.sum_apply,smul_eq_mul]
  intro P pd
  rw [← app P]
  rw [P.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le pd),map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hJ : J ((X:K[X])^j) = A ((X:K[X])^j) := by
    rw [app]
    simpa only [eval_pow,eval_X] using mon j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  rw [← Polynomial.smul_eq_C_mul,map_smul,map_smul,hJ]

theorem exactRule_mapField {ι : Type*} {J : K[X] →ₗ[K] K} {J' : L[X] →ₗ[L] L}
    {s : Finset ι} {v μ : ι → K} {d : ℕ} (e : K →+* L)
    (commute : ∀ P : K[X], J' (P.map e) = e (J P))
    (law : ExactRule J s v μ d) :
    ExactRule J' s (e ∘ v) (e ∘ μ) d := by
  apply exactRule_of_monomials
  intro n hn
  have hdeg : ((X:K[X])^n).natDegree ≤ d := by simpa only [natDegree_X_pow] using hn
  have he := congrArg (fun c : K => e c) (law _ hdeg)
  rw [← commute] at he
  simpa only [Polynomial.map_pow,map_X,map_sum,map_mul,map_pow,eval_pow,eval_X,
    Function.comp_apply] using he

theorem exactRule_mapSupport {ι η : Type*} {J : K[X] →ₗ[K] K}
    {s : Finset ι} {v μ : ι → K} {v' μ' : η → K} {d : ℕ}
    (emb : ι ↪ η) (nodes : ∀ i ∈ s, v' (emb i) = v i)
    (masses : ∀ i ∈ s, μ' (emb i) = μ i)
    (law : ExactRule J s v μ d) :
    ExactRule J (s.map emb) v' μ' d := by
  intro P hd
  rw [law P hd,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i hi
  rw [nodes i hi,masses i hi]

end
end RKCert.ReviewedNative.FiniteGaussianNodalLift

namespace RKCert.ReviewedNative.CrossedGaussianScalarLift

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteGaussianNodalLift
open RKCert.ReviewedNative.FiniteGaussianGridPositivity
open RKCert.ReviewedNative.CrossedGaussianSignedAdapter

noncomputable section
variable {K L : Type*} [Field K] [Field L]

theorem eval_at_mapped (e : K →+* L) (P : K[X]) (x : K) :
    (P.map e).eval (e x) = e (P.eval x) := by
  rw [eval_map,eval₂_at_apply]

section CharZero

variable [CharZero K] [CharZero L]

theorem formalPrimitive_map (e : K →+* L) (P : K[X]) :
    (formalPrimitive P).map e = formalPrimitive (P.map e) := by
  apply eq_of_derivative_and_eval_zero
  · simp only [derivative_map,derivative_formalPrimitive]
  · calc
      ((formalPrimitive P).map e).eval 0 = e ((formalPrimitive P).eval 0) := by
        simpa only [map_zero] using eval_at_mapped e (formalPrimitive P) 0
      _ = (formalPrimitive (P.map e)).eval 0 := by simp

theorem integral_map (e : K →+* L) (l r : K) (P : K[X]) :
    integral (e l) (e r) (P.map e) = e (integral l r P) := by
  simp only [integral_apply,← formalPrimitive_map e P,eval_at_mapped,map_sub]

theorem intervalPoint_map (e : K →+* L) (l r : K) (i : Fin 19) :
    intervalPoint (e l) (e r) i = e (intervalPoint l r i) := by
  simp only [intervalPoint,point,map_add,map_sub,map_mul,map_div₀,map_natCast,map_ofNat]

end CharZero

section Ordered

variable [LinearOrder K] [IsStrictOrderedRing K] [LinearOrder L] [IsStrictOrderedRing L]

theorem unitMoment_map (e : K →+* L) (q P : K[X]) :
    unitMoment (q.map e) (P.map e) = e (unitMoment q P) := by
  rw [unitMoment_apply,unitMoment_apply,← integral_map]
  simp only [unitWeight,Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_one,map_X,
    map_zero,map_one]

/-- The dose of exactness carried from the original ordered base to a
coefficient field containing selected root factors. -/
theorem unitMoment_map_signedRule (e : K →+* L)
    {old : Finset K} {μ : K → K} {μ' : L → L} {d : ℕ} (q : K[X])
    (mass : ∀ x ∈ old, μ' (e x) = e (μ x))
    (law : ExactRule (unitMoment q) old id μ d) :
    ExactRule (unitMoment (q.map e)) (old.map ⟨e,e.injective⟩) id μ' d := by
  have result := exactRule_mapField e (unitMoment_map e q) law
  exact exactRule_mapSupport (⟨e,e.injective⟩ : K ↪ L)
    (fun _ _ => rfl) mass result

/-- Preserve positivity on two selected finite meshes by expressing each
target node as the image of its own base-field node. -/
theorem intervalGrid_nonneg_of_base (e : K →+* L) (B : L[X])
    (base : ∀ x : K, 0 ≤ x → x ≤ 1 → 0 ≤ B.eval (e x))
    {l r : K} (l0 : 0≤l) (r1 : r≤1) (lr : l<r) :
    ∀ i : Fin 19, 0 ≤ B.eval (intervalPoint (e l) (e r) i) := by
  intro i
  rw [intervalPoint_map]
  have inside := intervalPoint_mem lr i
  exact base _ (l0.trans inside.1.le) (inside.2.le.trans r1)

end Ordered

end
end RKCert.ReviewedNative.CrossedGaussianScalarLift
