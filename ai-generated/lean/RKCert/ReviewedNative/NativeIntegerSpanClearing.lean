module

public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Int.Cast.Lemmas
import Init.Data.List.FinRange

@[expose] public section

/-! Sparse exact integer coordinates and sound rational-span receipt.
The executable part has no rational arithmetic or choice of basis. -/
namespace RKResearch.Certified.NativeIntegerSpanClearing

abbrev ZVec (s : ℕ) := Fin s → ℤ
abbrev ZFeature (s : ℕ) := ZVec s × ℤ
abbrev QFeature (s : ℕ) := (Fin s → ℚ) × ℚ

structure Clearing (r : ℕ) where
  denominator : ℤ
  terms : List (Fin r × ℤ)

def checkIndices {r : ℕ} (test : Fin r → Bool) : Bool :=
  (List.finRange r).all test

theorem checkIndices_get {r : ℕ} {test : Fin r → Bool}
    (h : checkIndices test = true) (i : Fin r) : test i = true := by
  change (List.finRange r).all test = true at h
  exact List.all_eq_true.mp h i (List.mem_finRange i)

def checkVec {s : ℕ} (x y : ZVec s) : Bool :=
  checkIndices fun i => decide (x i = y i)

theorem checkVec_sound {s : ℕ} {x y : ZVec s} (h : checkVec x y = true) :
    x = y := by
  change checkIndices (fun i => decide (x i = y i)) = true at h
  funext i
  exact of_decide_eq_true (checkIndices_get h i)

def checkFeature {s : ℕ} (x y : ZFeature s) : Bool :=
  checkVec x.1 y.1 && decide (x.2 = y.2)

theorem checkFeature_sound {s : ℕ} {x y : ZFeature s}
    (h : checkFeature x y = true) : x = y := by
  change (checkVec x.1 y.1 && decide (x.2 = y.2)) = true at h
  obtain ⟨hs, ht⟩ := Bool.and_eq_true_iff.mp h
  exact Prod.ext (checkVec_sound hs) (of_decide_eq_true ht)

def checkTermList {r : ℕ} : Option (Fin r) → List (Fin r × ℤ) → Bool
  | _, [] => true
  | previous, t :: ts =>
      decide (t.2 ≠ 0) &&
        ((match previous with
          | none => true
          | some i => decide (i < t.1)) &&
         checkTermList (some t.1) ts)

def scaleZ {s : ℕ} (c : ℤ) (x : ZFeature s) : ZFeature s :=
  (fun i => c*x.1 i, c*x.2)

def addZ {s : ℕ} (x y : ZFeature s) : ZFeature s :=
  (fun i => x.1 i+y.1 i, x.2+y.2)

def sparseSum {s r : ℕ} (rows : Fin r → ZFeature s) :
    List (Fin r × ℤ) → ZFeature s
  | [] => 0
  | t :: ts => addZ (scaleZ t.2 (rows t.1)) (sparseSum rows ts)

/-- All stage coordinates and the last homogeneous coordinate are checked.
Key uniqueness/order are checked as part of the canonical sparse format. -/
def checkClearing {s r : ℕ} (rows : Fin r → ZFeature s)
    (x : ZFeature s) (p : Clearing r) : Bool :=
  decide (0 < p.denominator) &&
    (checkTermList none p.terms &&
      checkFeature (scaleZ p.denominator x) (sparseSum rows p.terms))

def ratVec {s : ℕ} (x : ZVec s) : Fin s → ℚ := (Int.castRingHom ℚ) ∘ x

def ratFeature {s : ℕ} (x : ZFeature s) : QFeature s :=
  (ratVec x.1, (x.2 : ℚ))

theorem ratFeature_scaleZ {s : ℕ} (a : ℤ) (x : ZFeature s) :
    ratFeature (scaleZ a x) = (a : ℚ) • ratFeature x := by
  apply Prod.ext
  · funext i
    change ((a*x.1 i : ℤ) : ℚ) = (a : ℚ) * (x.1 i : ℚ)
    exact Int.cast_mul _ _
  · change ((a*x.2 : ℤ) : ℚ) = (a : ℚ) * (x.2 : ℚ)
    exact Int.cast_mul _ _

theorem ratFeature_addZ {s : ℕ} (x y : ZFeature s) :
    ratFeature (addZ x y) = ratFeature x + ratFeature y := by
  apply Prod.ext
  · funext i
    change ((x.1 i + y.1 i : ℤ) : ℚ) = (x.1 i : ℚ) + (y.1 i : ℚ)
    exact Int.cast_add _ _
  · change ((x.2 + y.2 : ℤ) : ℚ) = (x.2 : ℚ) + (y.2 : ℚ)
    exact Int.cast_add _ _

theorem ratFeature_zero (s : ℕ) : ratFeature (0 : ZFeature s) = 0 := by
  apply Prod.ext
  · funext i
    change ((0 : ℤ) : ℚ) = 0
    exact Int.cast_zero
  · change ((0 : ℤ) : ℚ) = 0
    exact Int.cast_zero

theorem sparseSum_mem_span {s r : ℕ} (rows : Fin r → ZFeature s)
    (terms : List (Fin r × ℤ)) :
    ratFeature (sparseSum rows terms) ∈
      Submodule.span ℚ (Set.range (fun i => ratFeature (rows i))) := by
  induction terms with
  | nil =>
    change ratFeature (0 : ZFeature s) ∈ _
    rw [ratFeature_zero]
    exact Submodule.zero_mem _
  | cons t ts ih =>
    rw [sparseSum, ratFeature_addZ, ratFeature_scaleZ]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨t.1, rfl⟩)) ih

/-- A successful closed integer receipt proves true membership over ℚ,
not merely membership up to some unchecked nonzero multiple. -/
theorem checkClearing_sound {s r : ℕ} {rows : Fin r → ZFeature s}
    {x : ZFeature s} {p : Clearing r} (h : checkClearing rows x p = true) :
    ratFeature x ∈ Submodule.span ℚ (Set.range (fun i => ratFeature (rows i))) := by
  simp only [checkClearing, Bool.and_eq_true_iff] at h
  obtain ⟨hd, _, he⟩ := h
  have pos : 0 < p.denominator := of_decide_eq_true hd
  have nz : (p.denominator : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ne_of_gt pos)
  have eqZ := checkFeature_sound he
  have eqQ : (p.denominator : ℚ) • ratFeature x =
      ratFeature (sparseSum rows p.terms) := by
    simpa only [ratFeature_scaleZ] using congrArg ratFeature eqZ
  let S := Submodule.span ℚ (Set.range (fun i => ratFeature (rows i)))
  have hsmul : (p.denominator : ℚ) • ratFeature x ∈ S := by
    rw [eqQ]
    exact sparseSum_mem_span rows p.terms
  simpa only [smul_smul, inv_mul_cancel₀ nz, one_smul] using
    S.smul_mem ((p.denominator : ℚ)⁻¹) hsmul

end RKResearch.Certified.NativeIntegerSpanClearing
