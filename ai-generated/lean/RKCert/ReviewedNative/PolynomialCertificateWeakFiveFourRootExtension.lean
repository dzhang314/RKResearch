module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveEightRootSector
public import Mathlib.Data.Finset.Sort

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Four physical quartic roots over an arbitrary ordered extension

There is no unjustified IVT in the base field. The scalar data are
transported to the field of the four true roots. Six base monomial
equations span *all* degree-at-most-five tests in the larger field.
-/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.WeakFive16
open scoped Polynomial BigOperators

variable {K L : Type*} [Field K] [Field L] [LinearOrder K] [IsStrictOrderedRing K]
  [LinearOrder L] [IsStrictOrderedRing L]

theorem map_formal_primitive (f : K →+* L) (p : K[X]) :
    (formalPrimitive p).map f = formalPrimitive (p.map f) := by
  apply eq_of_derivative_and_eval_zero
  · rw [derivative_map, derivative_formalPrimitive, derivative_formalPrimitive]
  · have at_zero := Polynomial.eval_map_apply (p := formalPrimitive p) (f := f) 0
    simpa only [map_zero, formalPrimitive_eval_zero] using at_zero

theorem integral_along_field (f : K →+* L) (l r : K) (p : K[X]) :
    integral (f l) (f r) (p.map f) = f (integral l r p) := by
  rw [integral_apply, integral_apply, ← map_formal_primitive, map_sub,
    Polynomial.eval_map_apply, Polynomial.eval_map_apply]

theorem nodalTail_along_field (f : K →+* L) (c : Fin 5 → K) (Z : K[X]) :
    (nodalTail c Z).map f = nodalTail (fun i => f (c i)) (Z.map f) := by simp [nodalTail]

theorem moments_along_field {q Z : K[X]} {c : Fin 5 → K} (f : K →+* L) (M : Moments q Z c) :
    Moments (q.map f) (Z.map f) (fun i => f (c i)) := by
  have send (l r : K) (p : K[X]) (paid : integral l r p = 0) :
      integral (f l) (f r) (p.map f) = 0 := by rw [integral_along_field, paid, map_zero]
  refine ⟨Polynomial.map_ne_zero M.qNonzero, (natDegree_map_le).trans M.qDegree, ?_,
    f.injective.comp M.clockSimple, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [M.origin, map_zero]
  · intro i
    constructor
    · intro eq
      exact (M.active i).1 (f.injective (eq.trans (map_one f).symm))
    · rw [Polynomial.eval_map_apply]
      exact fun eq => (M.active i).2 (f.injective (eq.trans (map_zero f).symm))
  · rw [M.middleFactor]
    simp
  · simpa using send _ _ _ M.forwardFirst
  · simpa using send _ _ _ M.forwardSecond
  · simpa using send _ _ _ M.forwardInner
  · simpa using send _ _ _ M.reverseFirst
  · simpa using send _ _ _ M.reverseSecond
  · simpa using send _ _ _ M.reverseInner
  · intro H small
    let N := q.map f * nodalTail (fun i => f (c i)) (Z.map f)
    let F : L[X] →ₗ[L] L := (integral 0 1).comp (LinearMap.mulLeft L (X*(1-X)*N))
    have powers (k : ℕ) (hk : k < 6) : F (X^k) = 0 := by
      have base := M.weightedMoments (X^k) (by rw [natDegree_X_pow]; omega)
      change integral 0 1 (X*(1-X)*N*X^k) = 0
      simpa [N, nodalTail_along_field] using send _ _ _ base
    change F H = 0
    rw [H.as_sum_range' 6 (by omega), map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, powers i (Finset.mem_range.mp hi),
      smul_zero]

/-- The four supplied roots need not be in increasing order. They are
disjoint from the marks by the original activity field, not an extra hypothesis. -/
theorem no_four_distinct_interior_roots {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (marks : ∀ i : Fin 4, c i.succ ∈ Set.Ioo 0 1) {r : Fin 4 → K}
    (distinct : Function.Injective r) (inside : ∀ i, r i ∈ Set.Ioo 0 1)
    (rq : ∀ i, q.IsRoot (r i)) : False := by
  classical
  let mark : Fin 4 → K := fun i => c i.succ
  let R : Finset K := Finset.univ.image r
  let A : Finset K := Finset.univ.image mark
  let S := R ∪ A
  have mi : Function.Injective mark := M.clockSimple.comp (Fin.succ_injective 4)
  have cardR : R.card = 4 := by simp [R, Finset.card_image_of_injective _ distinct]
  have cardA : A.card = 4 := by simp [A, Finset.card_image_of_injective _ mi]
  have dis : Disjoint R A := by
    apply Finset.disjoint_left.mpr
    intro x hr hm
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hr
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    apply (M.active i.succ).2
    exact (congrArg (fun v => q.eval v) (hi.trans hj.symm)).trans (rq j)
  have cardS : S.card = 8 := by
    change (R ∪ A).card = 8
    rw [Finset.card_union_of_disjoint dis, cardR, cardA]
  let β : Fin 8 → K := S.orderEmbOfFin cardS
  have mem (i : Fin 8) : β i ∈ R ∨ β i ∈ A := Finset.mem_union.mp (S.orderEmbOfFin_mem cardS i)
  have ri (j : Fin 4) : (q*nodalTail c Z).IsRoot (r j) := by
    have zero : q.eval (r j) = 0 := rq j
    simp only [IsRoot, eval_mul, zero, zero_mul]
  have ai (j : Fin 4) : (q*nodalTail c Z).IsRoot (mark j) := by
    fin_cases j <;> norm_num [mark, IsRoot, nodalTail, M.middleFactor]
  apply no_moments_with_eight_interior_sites M (S.orderEmbOfFin cardS).strictMono
  · intro i
    rcases mem i with hr | ha
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hr
      change β i ∈ Set.Ioo 0 1
      rw [← hj]
      exact inside j
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp ha
      change β i ∈ Set.Ioo 0 1
      rw [← hj]
      exact marks j
  · intro i
    rcases mem i with hr | ha
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hr
      change (q*nodalTail c Z).IsRoot (β i)
      rw [← hj]
      exact ri j
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp ha
      change (q*nodalTail c Z).IsRoot (β i)
      rw [← hj]
      exact ai j

/-- Actual source-level interior four-change exclusion: if the required
quartic roots lie in a larger ordered field, the paid packet maps there
first. No ordering of marks or original-field root extraction is assumed. -/
theorem no_four_interior_roots_in_ordered_extension {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (f : K →+* L) (ordered : StrictMono f)
    (marks : ∀ i : Fin 4, c i.succ ∈ Set.Ioo 0 1) {r : Fin 4 → L}
    (distinct : Function.Injective r) (inside : ∀ i, r i ∈ Set.Ioo 0 1)
    (qr : ∀ i, (q.map f).IsRoot (r i)) : False := by
  apply no_four_distinct_interior_roots (moments_along_field f M) _ distinct inside qr
  intro i
  exact ⟨by simpa only [map_zero] using ordered (marks i).1,
    by simpa only [map_one] using ordered (marks i).2⟩

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
