module

public import RKCert.ReviewedNative.NonsingularDIRKStageFloor
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

public section

/-! # Unit endpoints in five-stage common-diagonal order five

A last stage of zero weight is deletable. A zero first tap makes the
first two rows duplicates, so they merge. Both reductions preserve the
full reviewed order and contradict the four-stage obstruction. A
nonunit in any coefficient ring can be killed in a maximal residue
field, proving that both quantities are units before specializing.
No weighted transpose or signed form is used.
-/
namespace RKResearch.Certified.SDIRKFiveEndpointUnits

universe u
open scoped Matrix
open FiniteRootedTree

section Deletion

variable {R : Type*} [CommSemiring R]
  {A : Matrix (Fin 5) (Fin 5) R} {b : Fin 5 → R}

private theorem delete_order (hA : A.IsLowerTriangular) (hb : b (Fin.last 4) = 0)
    {p : ℕ} (ho : HasOrder p A b) :
    HasOrder p (A.submatrix Fin.castSucc Fin.castSucc) (b ∘ Fin.castSucc) := by
  let B := A.submatrix (Fin.castSucc : Fin 4 → Fin 5) (Fin.castSucc : Fin 4 → Fin 5)
  have hact (x : Fin 5 → R) (i : Fin 4) :
      (A *ᵥ x) i.castSucc = (B *ᵥ (x ∘ Fin.castSucc)) i := by
    rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_castSucc]
    have hz : A i.castSucc (Fin.last 4) = 0 := hA (Fin.castSucc_lt_last i)
    rw [hz, zero_mul, add_zero]
    rfl
  have stage (t : FiniteRootedTree) (i : Fin 4) :
      Φ t A i.castSucc = Φ t B i := by
    induction t generalizing i with
    | leaf => rfl
    | butcherProduct t r ih₁ ih₂ =>
      simp only [Φ, Pi.mul_apply, ih₁, hact]
      rw [show Φ r A ∘ Fin.castSucc = Φ r B from funext ih₂]
  intro t ht
  have h := ho t ht
  have hrow : b ⬝ᵥ Φ t A = (b ∘ Fin.castSucc) ⬝ᵥ Φ t B := by
    rw [dotProduct, dotProduct, Fin.sum_univ_castSucc, hb, zero_mul, add_zero]
    simp only [Function.comp_apply, stage]
  rw [hrow] at h
  exact h

end Deletion

section Merge

variable {R : Type*} [CommSemiring R]

private def pr : Fin 5 → Fin 4 := ![0,0,1,2,3]
private def rep : Fin 4 → Fin 5 := ![0,2,3,4]

private theorem rep_strict : StrictMono rep := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private def merged (A : Matrix (Fin 5) (Fin 5) R) : Matrix (Fin 4) (Fin 4) R :=
  Matrix.of fun i j => if j = 0 then A (rep i) 0 + A (rep i) 1 else A (rep i) (rep j)

private def mergedWeights (b : Fin 5 → R) : Fin 4 → R :=
  fun j => if j = 0 then b 0 + b 1 else b (rep j)

private theorem representative_action (A : Matrix (Fin 5) (Fin 5) R) (x : Fin 4 → R)
    (i : Fin 4) : (A *ᵥ (x ∘ pr)) (rep i) = (merged A *ᵥ x) i := by
  simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Function.comp_apply, add_zero]
  change A (rep i) 0*x 0+(A (rep i) 1*x 0+(A (rep i) 2*x 1+
    (A (rep i) 3*x 2+A (rep i) 4*x 3))) =
     (A (rep i) 0+A (rep i) 1)*x 0+(A (rep i) 2*x 1+
      (A (rep i) 3*x 2+A (rep i) 4*x 3))
  rw [add_mul, add_assoc]

private theorem merge_top_action {A : Matrix (Fin 5) (Fin 5) R} {γ : R}
    (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ) (h10 : A 1 0 = 0)
    (x : Fin 4 → R) : (A *ᵥ (x ∘ pr)) 1 = (A *ᵥ (x ∘ pr)) 0 := by
  simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Function.comp_apply, add_zero]
  change A 1 0*x 0+(A 1 1*x 0+(A 1 2*x 1+(A 1 3*x 2+A 1 4*x 3))) =
    A 0 0*x 0+(A 0 1*x 0+(A 0 2*x 1+(A 0 3*x 2+A 0 4*x 3)))
  have h12 := @ha (1 : Fin 5) 2 (by decide)
  have h13 := @ha (1 : Fin 5) 3 (by decide)
  have h14 := @ha (1 : Fin 5) 4 (by decide)
  have h01 := @ha (0 : Fin 5) 1 (by decide)
  have h02 := @ha (0 : Fin 5) 2 (by decide)
  have h03 := @ha (0 : Fin 5) 3 (by decide)
  have h04 := @ha (0 : Fin 5) 4 (by decide)
  simp only [h10, he, h12, h13, h14, h01, h02, h03, h04,
    zero_mul, add_zero, zero_add]

private theorem merge_action {A : Matrix (Fin 5) (Fin 5) R} {γ : R}
    (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ) (h10 : A 1 0 = 0)
    (x : Fin 4 → R) : A *ᵥ (x ∘ pr) = (merged A *ᵥ x) ∘ pr := by
  funext i
  change (A *ᵥ (x ∘ pr)) i = (merged A *ᵥ x) (pr i)
  rw [← representative_action]
  fin_cases i <;> first | rfl | exact merge_top_action ha he h10 x

private theorem merge_readout (b : Fin 5 → R) (x : Fin 4 → R) :
    b ⬝ᵥ (x ∘ pr) = mergedWeights b ⬝ᵥ x := by
  simp only [dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, Function.comp_apply, add_zero]
  change b 0*x 0+(b 1*x 0+(b 2*x 1+(b 3*x 2+b 4*x 3))) =
    (b 0+b 1)*x 0+(b 2*x 1+(b 3*x 2+b 4*x 3))
  rw [add_mul, add_assoc]

private theorem merge_order {A : Matrix (Fin 5) (Fin 5) R} {b : Fin 5 → R} {γ : R}
    (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ) (h10 : A 1 0 = 0)
    {p : ℕ} (ho : HasOrder p A b) : HasOrder p (merged A) (mergedWeights b) := by
  have hΦ (t : FiniteRootedTree) : Φ t A = Φ t (merged A) ∘ pr := by
    induction t with
    | leaf => rfl
    | butcherProduct t r h₁ h₂ =>
      simp only [Φ, h₁, h₂, merge_action ha he h10]
      rfl
  intro t ht
  have hh := ho t ht
  rw [hΦ, merge_readout] at hh
  exact hh

private theorem merge_triangular {A : Matrix (Fin 5) (Fin 5) R}
    (ha : A.IsLowerTriangular) : (merged A).IsLowerTriangular := by
  intro i j hij
  have hn : j ≠ 0 := ne_of_gt ((Fin.zero_le i).trans_lt hij)
  change (if j = 0 then A (rep i) 0 + A (rep i) 1 else A (rep i) (rep j)) = 0
  have hh : (if j = 0 then A (rep i) 0 + A (rep i) 1 else A (rep i) (rep j)) =
      A (rep i) (rep j) := by simp [hn]
  rw [hh]
  exact @ha (rep i) (rep j) (rep_strict hij)

private theorem merge_diagonal {A : Matrix (Fin 5) (Fin 5) R} {γ : R}
    (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ) (i : Fin 4) :
    merged A i i = γ := by
  by_cases hi : i = 0
  · subst i
    change A 0 0 + A 0 1 = γ
    have h01 := @ha (0 : Fin 5) 1 (by decide)
    rw [he, h01, add_zero]
  · simp [merged, hi, he]

end Merge

private theorem isUnit_of_field_images {R : Type u} [CommRing R] (x : R)
    (h : ∀ (K : Type u) [Field K] (f : R →+* K), f x ≠ 0) : IsUnit x := by
  by_contra hn
  let J : Ideal R := Ideal.span ({x} : Set R)
  have hJ : J ≠ ⊤ := fun e => hn (Ideal.span_singleton_eq_top.mp e)
  obtain ⟨I,hI,hJI⟩ := Ideal.exists_le_maximal J hJ
  let := hI
  let := Ideal.Quotient.field I
  have hz : Ideal.Quotient.mk I x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hJI (Ideal.subset_span (by simp)))
  exact h (R ⧸ I) (Ideal.Quotient.mk I) hz

variable {R : Type u} [CommRing R]
  {A : Matrix (Fin 5) (Fin 5) R} {b : Fin 5 → R} {γ : R}

/-- The last output weight in a five-stage common-diagonal order-five
tableau is a unit. This includes the possibility of a zero diagonal. -/
theorem last_weight_unit (ho : HasOrder 5 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i, A i i = γ) : IsUnit (b (Fin.last 4)) := by
  apply isUnit_of_field_images
  intro K _ f hb
  let B := (A.map f).submatrix (Fin.castSucc : Fin 4 → Fin 5) (Fin.castSucc : Fin 4 → Fin 5)
  have horder : HasOrder 5 B ((f ∘ b) ∘ Fin.castSucc) :=
    delete_order (ha.map f) hb (ho.map f)
  have htri : B.IsLowerTriangular := by
    intro i j hij
    change (A.map f) i.castSucc j.castSucc = 0
    exact (ha.map f) (Fin.castSucc_lt_castSucc_iff.mpr hij)
  have hdiag (i : Fin 4) : B i i = f γ := congrArg f (he i.castSucc)
  have h := horder.common_diagonal_order_five_stages htri hdiag
  omega

/-- The first strict-lower coefficient, equivalently the difference
of the first two clocks, is a unit in any coefficient ring. -/
theorem first_tap_unit (ho : HasOrder 5 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i, A i i = γ) : IsUnit (A 1 0) := by
  apply isUnit_of_field_images
  intro K _ f hx
  have he' (i : Fin 5) : (A.map f) i i = f γ := congrArg f (he i)
  have horder := merge_order (ha.map f) he' hx (ho.map f)
  have h := horder.common_diagonal_order_five_stages (merge_triangular (ha.map f))
    (merge_diagonal (ha.map f) he')
  omega

/-- Direct clock form of the first-tap obstruction. -/
theorem first_clock_gap_unit (ho : HasOrder 5 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i, A i i = γ) : IsUnit ((A *ᵥ 1) 1 - (A *ᵥ 1) 0) := by
  have e0 : (A *ᵥ 1) 0 = γ := by
    rw [lowerTriangular_mulVec_pivot ha 0 1 (fun j hj => (Fin.not_lt_zero j hj).elim),
      he, Pi.one_apply, mul_one]
  have e1 : (A *ᵥ 1) 1 = A 1 0 + γ := by
    have h12 := @ha (1 : Fin 5) 2 (by decide)
    have h13 := @ha (1 : Fin 5) 3 (by decide)
    have h14 := @ha (1 : Fin 5) 4 (by decide)
    simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_succ, Fin.sum_univ_zero, Pi.one_apply,
      mul_one, add_zero]
    change A 1 0 + (A 1 1 + (A 1 2 + (A 1 3 + A 1 4))) = _
    simp only [he, h12, h13, h14, add_zero]
  rw [e0,e1,add_sub_cancel_right]
  exact first_tap_unit ho ha he

end RKResearch.Certified.SDIRKFiveEndpointUnits
